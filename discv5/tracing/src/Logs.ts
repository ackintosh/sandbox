import { tracing } from './generated/proto';
import {LogKeyHelper} from "./LogKeyHelper";

export class Logs {
    first_key: string | null;
    last_key: string | null;
    logs: Map<string, Array<tracing.Log>>;

    constructor() {
        this.first_key = null;
        this.last_key = null;
        this.logs = new Map();
    }

    private static key(log: tracing.Log): string {
        if (log.timestamp == undefined || log.timestamp.nanos == null) {
            throw new Error(`invalid log: ${log}`);
        }

        const milli = `0000${Math.floor(log.timestamp.nanos / 1000000).toString()}`.slice(-4);
        return `${log.timestamp.seconds}${milli}`;
    }

    add(log: tracing.Log): void {
        const t = Logs.key(log);
        const elements = this.logs.get(t);
        if (elements !== undefined) {
            elements.push(log);
            this.logs.set(t, elements);
        } else {
            this.logs.set(t, [log]);
        }

        // if (this.logs.has(t)) {
        //     const elements = this.logs.get(t);
        //     elements.push(log);
        //     this.logs.set(t, elements);
        // } else {
        //     this.logs.set(t, [log]);
        // }
    }

    sort() {
        const sorted = Array.from(this.logs).sort(([k, _v], [k2, _v2]) => {
            this.updateEdgeKey(k);
            this.updateEdgeKey(k2);
            if (k > k2) {
                this.last_key = k;
                return 1;
            } else {
                this.first_key = k;
                return -1;
            }
        });


        this.logs = new Map(sorted);
    }

    slice(time: string, progress: number): Array<tracing.Log> {
        let slice: Array<tracing.Log> = [];

        let k = time;
        for (let i = 0; i < progress; i++) {
            const logs = this.logs.get(k);
            if (logs !== undefined) {
                slice = slice.concat(logs);
            }
            k = LogKeyHelper.increment(k);
        }

        return slice;
    }

    updateEdgeKey(k: string): void {
        if (this.first_key === null) {
            this.first_key = k;
        }

        if (this.last_key === null) {
            this.last_key = k;
        }

        if (this.first_key !== null && this.first_key > k) {
            this.first_key = k;
        }

        if (this.last_key !== null && this.last_key < k) {
            this.last_key = k;
        }
    }
}
