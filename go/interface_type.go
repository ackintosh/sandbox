package main

import "fmt"

type TestInterface interface {
	Foo() string
}

type TestStruct struct {
}

func (t TestStruct) Foo() string {
	return "test string"
}

type FooStruct struct {
}

func (t FooStruct) Foo() string {
	return "foo string"
}

func printStructName(t TestInterface) {
	switch entity := t.(type) {
	case TestStruct:
		fmt.Println("TestStruct")
		fmt.Println(entity.Foo())
	case FooStruct:
		fmt.Println("FooStruct")
		fmt.Println(entity.Foo())
	default:
		fmt.Println("Unknown")
	}
}

func main() {
	var testStruct = TestStruct{}
	printStructName(testStruct)

	var fooStruct = FooStruct{}
	printStructName(fooStruct)
}
