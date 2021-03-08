package main

import (
	"fmt"
	"time"
)

func main() {
	ch := produce()

	fmt.Println("sleep ->")
	time.Sleep(time.Second * 3)
	fmt.Println("<- sleep")

	for i := range ch {
		fmt.Println(i)
	}
}

func produce() chan int {
	ch := make(chan int, 10)

	go func() {
		defer func() {
			fmt.Println("produce::defer")
			close(ch)
		}()

		i := 0
		for {
			if i > 5 {
				break
			}
			fmt.Println("start: ch ", i)
			ch <- i
			fmt.Println("end: ch ", i)
			i++
		}
	}()

	return ch
}
