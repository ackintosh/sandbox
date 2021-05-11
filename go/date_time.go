package main

import (
	"fmt"
	"time"
)

func main() {
	t := time.Now()
	fmt.Println(t)

	timeZone := time.FixedZone("Asia/Tokyo", 9*60*60)
	fmt.Println(t.In(timeZone))
}
