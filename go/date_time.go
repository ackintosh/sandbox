package main

import (
	"fmt"
	"time"
)

// Goで時刻を扱うチートシート https://zenn.dev/hsaki/articles/go-time-cheatsheet

func main() {
	t := time.Now()
	fmt.Println(t)

	timeZone := time.FixedZone("Asia/Tokyo", 9*60*60)
	fmt.Println(t.In(timeZone))

	d := time.Date(2022, 11, 1, 8, 0, 0, 0, time.Local)
	fmt.Println(d) // 2022-11-01 08:00:00 +0900 JST
}
