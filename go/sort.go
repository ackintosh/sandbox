package main

import (
	"fmt"
	"sort"
)

type Person struct {
	Name string
	Age  int
}

func main() {
	people := []Person{
		{Name: "V", Age: 3},
		{Name: "K", Age: 3},
		{Name: "Y", Age: 3},
		{Name: "A", Age: 4},
		{Name: "E", Age: 3},
		{Name: "D", Age: 1},
		{Name: "C", Age: 3},
		{Name: "X", Age: 2},
		{Name: "B", Age: 3},
	}

	// sort.Slice
	// 安定ソートを保証しない （= もとの並び順を保証しない）
	sort.Slice(people, func(i, j int) bool { return people[i].Name < people[j].Name })
	fmt.Printf("NameでSort(Not-Stable):%+v\n", people)
}
