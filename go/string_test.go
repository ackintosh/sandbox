package main

import (
	"fmt"
	"strings"
	"testing"
)

func TestString(t *testing.T) {
	var strs = [...]string{
		"AAAAAAAAA",
		"AAAAAAAAA",
		"AAAAAAAAA",
		"AAAAAAAAA",
		"AAAAAAAAA",
		"AAAAAAAAA",
		"AAAAAAAAA",
	}

	var a = strings.Join(strs[:], ",")
	fmt.Println(a)
}

func TestSplit(t *testing.T) {
	s := "helloworld"
	fmt.Println(s[0:5])
	fmt.Println(s[5:])
}
