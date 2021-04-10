function hello(name: string): void {
    console.log("Hello " + name + "!");
}

let your_name: string = "Yamada";

class Sample {
  readonly name: string;

  constructor(name: string) {
    this.name = name;
  }
}

hello(your_name);

const sample = new Sample('mary');
console.log(sample.name);

// nameは readonly なので更新できない
// sample.name = 'bob';
// console.log(sample.name);
