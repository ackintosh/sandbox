class Counter {
  #i: number;

  constructor() {
    this.#i = 0;
  }

  increment(): void {
    this.#i++;
  }

  i(): number {
    return this.#i;
  }
}

class Sample {
  readonly name: string;
  readonly counter: Counter;

  constructor(name: string, counter: Counter) {
    this.name = name;
    this.counter = counter;
  }

  hello(): string {
    return `${this.name} ${this.counter.i()}`;
  }
}

const counter = new Counter();
counter.increment();
console.log(counter.i());

const sample = new Sample('mary', counter);
console.log(sample.hello());
counter.increment();
console.log(sample.hello());
