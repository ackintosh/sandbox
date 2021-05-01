import {Message, PacketType} from "./Message";

export class SentMessages {
  messages: Map<string, SentMessage>;

  constructor() {
    this.messages = new Map();
  }

  private add(message: SentMessage): void {
    this.messages.set(message.key(), message);
  }

  addOrdinaryMessage(sender: string, recipient: string, message: Message, step: number): void {
    const m = new SentMessage(sender, recipient, message, PacketType.Ordinary, step);
    this.add(m);
  }

  addHandshakeMessage(sender: string, recipient: string, message: Message, step: number): void {
    const m = new SentMessage(sender, recipient, message, PacketType.Handshake, step);
    this.add(m);
  }

  take(sender: string, recipient: string, requestId: string): SentMessage {
    const k = key(sender, requestId);
    const m = this.messages.get(k);

    if (m === undefined) {
      throw new Error(`[message not found] key: ${k}`);
    }

    if (m.recipient !== recipient) {
      throw new Error(`[message found but the recipient did not match] key: ${k}, m.recipient: ${m.recipient}, recipient: ${recipient}`);
    }

    this.messages.delete(k);
    return m;
  }
}

export class SentMessage {
  type: PacketType;
  sender: string;
  recipient: string;
  message: Message;
  step: number;

  constructor(sender, recipient, message, type: PacketType, step) {
    this.sender = sender;
    this.recipient = recipient;
    this.message = message;
    this.type = type;
    this.step = step;
  }

  key(): string {
    return key(this.sender, this.message.requestId());
  }
}

function key(sender: string, requestId: string): string {
  return `${sender}_${requestId}`;
}
