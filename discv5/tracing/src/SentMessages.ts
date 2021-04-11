import {Message} from "./Message";


export class SentMessages {
  messages: Map<string, SentMessage>;

  constructor() {
    this.messages = new Map();
  }

  add(sender: string, recipient: string, message: Message, step: number) {
    const m = new SentMessage(sender, recipient, message, step);
    this.messages.set(m.key(), m);
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
  sender: string;
  recipient: string;
  message: Message;
  step: number;

  constructor(sender, recipient, message, step) {
    this.sender = sender;
    this.recipient = recipient;
    this.message = message;
    this.step = step;
  }

  key() {
    return key(this.sender, this.message.requestId());
  }
}

function key(sender: string, requestId: string): string {
  return `${sender}_${requestId}`;
}
