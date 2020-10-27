package main

import "fmt"

func main() {
	test := map[string]string{}

	test["foo"] = "foo value"
	test["bar"] = "bar value"

	fmt.Println(test)
}
