package main

import "fmt"

func main() {
	m := map[string]int{"apple": 150, "banana": 300, "lemon": 300}

	apple, ok := m["apple"]
	fmt.Println(apple, ok)

	xxxx, ok := m["xxxx"]
	fmt.Println(xxxx, ok)

}
