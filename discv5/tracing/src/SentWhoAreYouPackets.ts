import {Long} from "protobufjs";

export class SentWhoAreYouPackets {
  packets: Map<string, SentWhoAreYou>;

  constructor() {
    this.packets = new Map();
  }

  add(sender: string, recipient: string, idNonce: Array<number>, enrSeq: number, step: number): void {
    const s = new SentWhoAreYou(sender, recipient, idNonce, enrSeq, step);
    this.packets.set(s.key(), s);
  }

  take(sender: string, recipient: string, enrSeq: number|Long): SentWhoAreYou {
    const k = key(sender, enrSeq);
    const m = this.packets.get(k);

    if (m === undefined) {
      throw new Error(`[whoareyou packet not found] key: ${k}`);
    }

    if (m.recipient !== recipient) {
      throw new Error(`[whoareyou packet found but the recipient did not match] key: ${k}, m.recipient: ${m.recipient}, recipient: ${recipient}`);
    }

    this.packets.delete(k);
    return m;
  }
}

export class SentWhoAreYou {
  sender: string;
  recipient: string;
  idNonce: Array<number>;
  enrSeq: number|Long;
  step: number;

  constructor(sender, recipient, idNonce, enrSeq, step) {
    this.sender = sender;
    this.recipient = recipient;
    this.idNonce = idNonce;
    this.enrSeq = enrSeq;
    this.step = step;
  }

  key(): string {
    return key(this.sender, this.enrSeq);
  }
}

function key(sender: string, enrSeq: number|Long): string {
  return `${sender}_${enrSeq}`;
}
