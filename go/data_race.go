package main

import (
	"fmt"
	"sync"
	"sync/atomic"
)

// Data Race Detector - The Go Programming Language
// https://golang.org/doc/articles/race_detector.html

// GoのRaceDetectorと気をつけるべき所｜株式会社CA Wise
// https://techblog.ca-wise.co.jp/2016/12/post-126.html

// 下記コマンドで実行する
// go run -race data_race.go

func main() {
	example1()
	fixed1()

	example2()
	fixed2()

}

/////////////////////////////////////////////////////////////////
// 複数のgoroutineからmapを更新している
/////////////////////////////////////////////////////////////////
func example1() {
	c := make(chan bool)
	m := make(map[string]string)
	go func() {
		m["1"] = "a"
		c <- true
	}()
	m["2"] = "b"
	<-c
	for k, v := range m {
		fmt.Println(k, v)
	}
}

// <修正後>
// mapの更新時にmutexを使って排他ロックする
func fixed1() {
	c := make(chan bool)
	var mu sync.Mutex
	m := make(map[string]string)
	go func() {
		mu.Lock()
		m["1"] = "a"
		mu.Unlock()

		c <- true
	}()

	mu.Lock()
	m["2"] = "b"
	mu.Unlock()

	<-c
	for k, v := range m {
		fmt.Println(k, v)
	}
}

/////////////////////////////////////////////////////////////////
// 複数のgoroutineからプリミティブ型を更新している
/////////////////////////////////////////////////////////////////
func example2() {
	c := make(chan bool)
	i := 0
	go func() {
		i = 1
		c <- true
	}()
	i = 9
	<-c
	fmt.Println(i)
}

// <修正後>
// intの場合、sync/atomic パッケージでアトミックな操作ができる
func fixed2() {
	c := make(chan bool)
	var i int64
	i = 0
	go func() {
		atomic.StoreInt64(&i, 1)

		// 読み込みは atomic.LoadInt64()
		// atomic.LoadInt64(&i)

		c <- true
	}()
	atomic.StoreInt64(&i, 9)
	<-c
	fmt.Println(i)
}
