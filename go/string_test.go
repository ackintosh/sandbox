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
