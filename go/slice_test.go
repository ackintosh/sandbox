package main

import (
	"fmt"
	"testing"
)

func Test(t *testing.T) {
	test := map[string]string{}

	test["foo"] = "foo value"
	test["bar"] = "bar value"

	fmt.Println(test)
}

// 2つのスライスを連結する
func TestAppendSliceToSlice(t *testing.T) {
	var slice_3 = []int{1, 2, 3, 4, 5, 6}
	var slice_4 = []int{7, 8}
	fmt.Printf("slice_4: %v\n", slice_4)

	slice_5 := append(slice_3, slice_4...)
	fmt.Printf("slice_5: %v\n", slice_5)
}
