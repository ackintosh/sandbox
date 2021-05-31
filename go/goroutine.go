package main

import (
	"fmt"
	"time"
)

/////////////////////////////////////////////
// チャンネルに値がセットされず、deadlockエラーが起きる例
/////////////////////////////////////////////
//func main() {
//	ch := make(chan int)
//
//	go func(ch chan int) {
//		rand.Seed(time.Now().UnixNano())
//		fmt.Println("go func")
//		n := rand.Intn(100)
//
//		fmt.Println("n: ", n)
//
//		if n % 2 == 0 {
//			return
//			// n が 偶数の場合、
//			// ここで return してしまい、 `res := <-ch` が終了しなくなってしまうため
//			// 下記エラーになる
//			// fatal error: all goroutines are asleep - deadlock!
//		}
//
//		ch <- 1
//
//	}(ch)
//
//	res := <-ch
//	fmt.Println(res)
//}

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
