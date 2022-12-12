package main

import (
	"fmt"
	"testing"
)

func TestPrint(t *testing.T) {
	type Person struct {
		Age    int
		Height int
	}

	p := new(Person)
	p.Age = 20
	p.Height = 180

	fmt.Printf("年齢: %d, 身長:%d\n", p.Age, p.Height)
	s := fmt.Sprintf("年齢: %d, 身長:%d\n", p.Age, p.Height)
	fmt.Print(s)
}
