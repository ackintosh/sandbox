import { tracing } from './generated/proto';
import {LogKeyHelper} from "./LogKeyHelper";

export class Logs {
    first_key: string;
    last_key: string;
    logs: Map<string, Array<tracing.Log>>;

    constructor() {
        this.first_key = undefined;
        this.last_key = undefined;
        this.logs = new Map();
    }

    private static key(log: tracing.Log): string {
        const milli = `0000${Math.floor(log.timestamp.nanos / 1000000).toString()}`.slice(-4);
        return `${log.timestamp.seconds}${milli}`;
    }

    add(log) {
        const t = Logs.key(log);

        if (this.logs.has(t)) {
            const elements = this.logs.get(t);
            elements.push(log);
            this.logs.set(t, elements);
        } else {
            this.logs.set(t, [log]);
        }
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

    slice(time, progress) {
        let slice = [];

        let k = time;
        for (let i = 0; i < progress; i++) {
            if (this.logs.has(k)) {
                slice = slice.concat(this.logs.get(k));
            }
            k = LogKeyHelper.increment(k);
        }

        return slice;
    }

    updateEdgeKey(k) {
        if (this.first_key === undefined) {
            this.first_key = k;
        }

        if (this.last_key === undefined) {
            this.last_key = k;
        }

        if (this.first_key > k) {
            this.first_key = k;
        }

        if (this.last_key < k) {
            this.last_key = k;
        }
    }
}
