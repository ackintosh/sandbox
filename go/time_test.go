package main

import (
	"fmt"
	"testing"
	"time"
)

// Goで時刻を扱うチートシート https://zenn.dev/hsaki/articles/go-time-cheatsheet
func TestBasics(t *testing.T) {
	now := time.Now()
	fmt.Println(now)

	timeZone := time.FixedZone("Asia/Tokyo", 9*60*60)
	fmt.Println(now.In(timeZone))

	d := time.Date(2022, 11, 1, 8, 0, 0, 0, time.Local)
	fmt.Println(d) // 2022-11-01 08:00:00 +0900 JST
}

// サンプルで学ぶ Go 言語：Time Formatting / Parsing
// https://www.spinute.org/go-by-example/time-formatting-parsing.html
func TestParse(t *testing.T) {
	// Format、Parse では例示に基づいてレイアウトを決める
	// ふつうは time モジュールに定義されている定数をレイアウトの例として使うが、独自のレイアウトを使ってもよい
	// レイアウトでは特定の時刻 Mon Jan 2 15:04:05 MST 2006 を表している必要があり、プログラムはこれに従って時刻をフォーマットしたり、文字列をパースしたりする

	// RFC3339 に対応するレイアウトを使う
	t1, _ := time.Parse(
		time.RFC3339,
		"2012-11-01T22:08:41+00:00")
	println(t1.String())

	// 独自のレイアウトを使う場合は、
	// Mon Jan 2 15:04:05 MST 2006 を表している必要がある
	layout := "2006-01-02T15:04:05+00:00"
	t2, _ := time.Parse(
		layout,
		"2012-11-01T22:08:41+00:00")
	println(t2.String())
}
