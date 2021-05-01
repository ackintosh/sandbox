import {Node} from './Node';
import {List, Table, Text} from "@arwes/core";

const COLOR_RANDOM: number = 0xffdd00;
const COLOR_PING: number = 0x0000ff;
const COLOR_PONG: number = 0xff00ff;
const COLOR_FINDNODE: number = 0x00d6dd;
const COLOR_NODES: number = 0xddd600;

export enum PacketType {
    Ordinary = 'Ordinary Message',
    Whoareyou = 'WHOAREYOU',
    Handshake = 'Handshake Message',
}

export interface Message {
    name(): string;
    color(): number;
    capText(): string;
    requestId(): string
    panelContents(type: PacketType): Object;
}

// https://github.com/ethereum/devp2p/blob/master/discv5/discv5-theory.md#step-1-node-a-sends-message-packet
export class Random implements Message{
    senderId: string;
    recipientId: string;

    constructor(sender: Node, recipient: Node) {
        this.senderId = sender.id;
        this.recipientId = recipient.id;
    }

    name(): string {
        return 'Random packet';
    }

    color(): number {
        return COLOR_RANDOM;
    }

    capText(): string {
        return '';
    }

    requestId(): string {
        throw new Error("Random has no requestId.");
    }

    panelContents(type: PacketType): Object {
        const headers = [
            { id: 'a', data: `${type}<${this.name()}>` }
        ];
        const dataset = [
            {
                id: 0,
                columns: [
                    {id: 0, data: 'sender'},
                    {id: 1, data: this.senderId},
                ],
            },
            {
                id: 1,
                columns: [
                    {id: 0, data: 'recipient'},
                    {id: 1, data: this.recipientId},
                ],
            },
        ];
        return <Table headers={headers} dataset={dataset}/>
    }
}

// https://github.com/ethereum/devp2p/blob/master/discv5/discv5-wire.md#ping-request-0x01
export class Ping implements Message{
    senderId: string;
    recipientId: string;
    readonly #requestId: string;
    enrSeq: number;

    constructor(
        sender: Node,
        recipient: Node,
        requestId: string,
        enrSeq: number
    ) {
        this.senderId = sender.id;
        this.recipientId = recipient.id;
        this.#requestId = requestId;
        this.enrSeq = enrSeq;
    }

    name(): string {
        return 'PING';
    }

    color(): number {
        return COLOR_PING;
    }

    capText(): string {
        return `  ${this.#requestId}\n  ${this.enrSeq}`;
    }

    requestId(): string {
        return this.#requestId;
    }

    panelContents(type: PacketType): Object {
        const headers = [
            { id: 'a', data: `${type}<${this.name()}>` }
        ];
        const dataset = [
            {
                id: 0,
                columns: [
                    {id: 0, data: 'sender'},
                    {id: 1, data: this.senderId},
                ],
            },
            {
                id: 1,
                columns: [
                    {id: 0, data: 'recipient'},
                    {id: 1, data: this.recipientId},
                ],
            },
            {
                id: 2,
                columns: [
                    {id: 0, data: 'request-id'},
                    {id: 1, data: this.requestId()},
                ],
            },
            {
                id: 3,
                columns: [
                    {id: 0, data: 'enr-seq'},
                    {id: 1, data: this.enrSeq},
                ],
            },
        ];
        return <Table headers={headers} dataset={dataset}/>
    }
}

// https://github.com/ethereum/devp2p/blob/master/discv5/discv5-wire.md#pong-response-0x02
export class Pong implements Message{
    senderId: string;
    recipientId: string;
    readonly #requestId: string;
    enrSeq: number;
    recipientIp: string;
    recipientPort: number;

    constructor(
        sender: Node,
        recipient: Node,
        requestId: string,
        enrSeq: number,
        recipientIp: string,
        recipientPort: number
    ) {
        this.senderId = sender.id;
        this.recipientId = recipient.id;
        this.#requestId = requestId;
        this.enrSeq = enrSeq;
        this.recipientIp = recipientIp;
        this.recipientPort = recipientPort;
    }

    name(): string {
        return 'PONG';
    }

    color(): number {
        return COLOR_PONG;
    }

    capText(): string {
        return `  ${this.#requestId}\n  ${this.enrSeq}\n  ${this.recipientIp}\n  ${this.recipientPort}`;
    }

    requestId(): string {
        return this.#requestId;
    }

    panelContents(type: PacketType): Object {
        const headers = [
            { id: 'a', data: `${type}<${this.name()}>` }
        ];
        const dataset = [
            {
                id: 0,
                columns: [
                    {id: 0, data: 'sender'},
                    {id: 1, data: this.senderId},
                ],
            },
            {
                id: 1,
                columns: [
                    {id: 0, data: 'recipient'},
                    {id: 1, data: this.recipientId},
                ],
            },
            {
                id: 2,
                columns: [
                    {id: 0, data: 'request-id'},
                    {id: 1, data: this.requestId()},
                ],
            },
            {
                id: 3,
                columns: [
                    {id: 0, data: 'enr-seq'},
                    {id: 1, data: this.enrSeq},
                ],
            },
            {
                id: 4,
                columns: [
                    {id: 0, data: 'recipient-ip'},
                    {id: 1, data: this.recipientIp},
                ],
            },
            {
                id: 5,
                columns: [
                    {id: 0, data: 'recipient-port'},
                    {id: 1, data: this.recipientPort},
                ],
            },
        ];
        return <Table headers={headers} dataset={dataset}/>
    }
}

// https://github.com/ethereum/devp2p/blob/master/discv5/discv5-wire.md#findnode-request-0x03
export class Findnode implements Message{
    senderId: string;
    recipientId: string;
    readonly #requestId: string;
    distances: Array<number>;

    constructor(
        sender: Node,
        recipient: Node,
        requestId: string,
        distances: Array<number>
    ) {
        this.senderId = sender.id;
        this.recipientId = recipient.id;
        this.#requestId = requestId;
        this.distances = distances;
    }

    name(): string {
        return 'FINDNODE';
    }

    color(): number {
        return COLOR_FINDNODE;
    }

    capText(): string {
        return `  ${this.#requestId}\n  [${this.distances.join(', ')}]`;
    }

    requestId(): string {
        return this.#requestId;
    }

    panelContents(type: PacketType): Object {
        const distanceList = [];
        for (let i = 0; i < this.distances.length; i++) {
            distanceList.push(<li key={this.distances[i]}><Text>{this.distances[i]}</Text></li>);
        }
        const headers = [
            { id: 'a', data: `${type}<${this.name()}>` }
        ];
        const dataset = [
            {
                id: 0,
                columns: [
                    {id: 0, data: 'sender'},
                    {id: 1, data: this.senderId},
                ],
            },
            {
                id: 1,
                columns: [
                    {id: 0, data: 'recipient'},
                    {id: 1, data: this.recipientId},
                ],
            },
            {
                id: 2,
                columns: [
                    {id: 0, data: 'request-id'},
                    {id: 1, data: this.requestId()},
                ],
            },
            {
                id: 3,
                columns: [
                    {id: 0, data: 'distances'},
                    {id: 1, data: <List>{distanceList}</List>},
                ],
            },
        ];
        return <Table headers={headers} dataset={dataset}/>
    }
}

// https://github.com/ethereum/devp2p/blob/master/discv5/discv5-wire.md#nodes-response-0x04
export class Nodes implements Message{
    senderId: string;
    recipientId: string;
    readonly #requestId: string;
    total: number;
    nodes: Array<string>;

    constructor(
        sender: Node,
        recipient: Node,
        requestId: string,
        total: number,
        nodes: Array<string>
    ) {
        this.senderId = sender.id;
        this.recipientId = recipient.id;
        this.#requestId = requestId;
        this.total = total;
        this.nodes = nodes;
    }

    name(): string {
        return 'NODES';
    }

    color(): number {
        return COLOR_NODES;
    }

    capText(): string {
        return `  ${this.#requestId}\n  ${this.total}\n  [${this.nodes.join(', ')}]`;
    }

    requestId(): string {
        return this.#requestId;
    }

    panelContents(type: PacketType): Object {
        const nodeList = [];
        for (let i = 0; i < this.nodes.length; i++) {
            nodeList.push(<li key={this.nodes[i]}><Text>{this.nodes[i]}</Text></li>);
        }
        const headers = [
            { id: 'a', data: `${type}<${this.name()}>` }
        ];
        const dataset = [
            {
                id: 0,
                columns: [
                    {id: 0, data: 'sender'},
                    {id: 1, data: this.senderId},
                ],
            },
            {
                id: 1,
                columns: [
                    {id: 0, data: 'recipient'},
                    {id: 1, data: this.recipientId},
                ],
            },
            {
                id: 2,
                columns: [
                    {id: 0, data: 'request-id'},
                    {id: 1, data: this.requestId()},
                ],
            },
            {
                id: 3,
                columns: [
                    {id: 0, data: 'total'},
                    {id: 1, data: this.total},
                ],
            },
            {
                id: 4,
                columns: [
                    {id: 0, data: 'nodes'},
                    {id: 1, data: <List>{nodeList}</List>},
                ],
            },
        ];
        return <Table headers={headers} dataset={dataset}/>
    }
}
