const COLOR_RANDOM = 0xffdd00;
const COLOR_PING = 0x0000ff;
const COLOR_PONG = 0xff00ff;
const COLOR_FINDNODE = 0x00d6dd;
const COLOR_NODES = 0xddd600;

export interface Message {
    name(): string;
    color(): number;
    capText(): string;
}

// https://github.com/ethereum/devp2p/blob/master/discv5/discv5-theory.md#step-1-node-a-sends-message-packet
export class Random implements Message{
    name() {
        return 'Random packet';
    }

    color() {
        return COLOR_RANDOM;
    }

    capText() {
        return '';
    }
}

// https://github.com/ethereum/devp2p/blob/master/discv5/discv5-wire.md#ping-request-0x01
export class Ping implements Message{
    requestId: string;
    enrSeq: number;

    constructor(requestId, enrSeq) {
        this.requestId = requestId;
        this.enrSeq = enrSeq;
    }

    name() {
        return 'PING';
    }

    color() {
        return COLOR_PING;
    }

    capText() {
        return `  ${this.requestId}\n  ${this.enrSeq}`;
    }
}

// https://github.com/ethereum/devp2p/blob/master/discv5/discv5-wire.md#pong-response-0x02
export class Pong implements Message{
    requestId: string;
    enrSeq: number;
    recipientIp: string;
    recipientPort: number;

    constructor(requestId, enrSeq, recipientIp, recipientPort) {
        this.requestId = requestId;
        this.enrSeq = enrSeq;
        this.recipientIp = recipientIp;
        this.recipientPort = recipientPort;
    }

    name() {
        return 'PONG';
    }

    color() {
        return COLOR_PONG;
    }

    capText() {
        return `  ${this.requestId}\n  ${this.enrSeq}\n  ${this.recipientIp}\n  ${this.recipientPort}`;
    }
}

// https://github.com/ethereum/devp2p/blob/master/discv5/discv5-wire.md#findnode-request-0x03
export class Findnode implements Message{
    requestId: string;
    distances: Array<number>;

    constructor(requestId, distances) {
        this.requestId = requestId;
        this.distances = distances;
    }

    name() {
        return 'FINDNODE';
    }

    color() {
        return COLOR_FINDNODE;
    }

    capText() {
        return `  ${this.requestId}\n  [${this.distances.join(', ')}]`;
    }
}

// https://github.com/ethereum/devp2p/blob/master/discv5/discv5-wire.md#nodes-response-0x04
export class Nodes implements Message{
    requestId: string;
    total: number;
    nodes: Array<string>;

    constructor(requestId, total, nodes) {
        this.requestId = requestId;
        this.total = total;
        this.nodes = nodes;
    }

    name() {
        return 'NODES';
    }

    color() {
        return COLOR_NODES;
    }

    capText() {
        return `  ${this.requestId}\n  ${this.total}\n  [${this.nodes.join(', ')}]`;
    }
}
