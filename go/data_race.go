package main

import "fmt"

// Data Race Detector - The Go Programming Language
// https://golang.org/doc/articles/race_detector.html

// go run -race data_race.go
func main() {
	c := make(chan bool)
	m := make(map[string]string)
	go func() {
		m["1"] = "a" // First conflicting access.
		c <- true
	}()
	m["2"] = "b" // Second conflicting access.
	<-c
	for k, v := range m {
		fmt.Println(k, v)
	}
}
