package main

import (
	"testing"
	"time"
)

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
