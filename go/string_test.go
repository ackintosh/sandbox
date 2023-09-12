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

func TestComparing(t *testing.T) {
	s1 := "00000000"
	s2 := "00000000_AR19652"

	println(s1 < s2) // true
}

func TestSplit(t *testing.T) {
	s := "helloworld"
	fmt.Println(s[0:5])
	fmt.Println(s[5:])
	// 最後の一文字
	fmt.Println(s[len(s)-1:])
}

func TestTrim(t *testing.T) {
	s := "helloworld"
	fmt.Println(strings.Trim(s, "he")) // lloworld

	fmt.Println(strings.TrimSpace("　全角スペース　"))
}
