package main

// 参考
// https://golang.hateblo.jp/entry/2018/11/08/231637

import (
	"encoding/json"
	"fmt"
	"io"
	"strings"
	"testing"
)

// Map -> JSON
func TestMapToJson(t *testing.T) {
	m := map[string]interface{}{
		"name": "Tanaka",
		"age":  30,
		"html": "<p>hello</p>",
	}

	data, err := json.Marshal(m)
	if err != nil {
		t.Error(err)
	}

	fmt.Println(string(data))
}

// Slice -> JSON
func TestSliceToJson(t *testing.T) {
	s := []string{"foo", "bar"}

	data, err := json.Marshal(s)
	if err != nil {
		t.Error(err)
	}

	fmt.Println(string(data))
}

// JSON -> struct
func TestJsonToStruct(t *testing.T) {
	data := `{
  "name": "Tanaka",
  "age": 30
}`

	var user struct {
		Name string `json:"name"`
		Age  int    `json:"age"`
	}

	d := json.NewDecoder(strings.NewReader(data))

	// // 構造体の場合に、JSONのキー名がその構造体に無い場合はエラーにする strict モード
	d.DisallowUnknownFields()

	err := d.Decode(&user)

	if err != nil && err != io.EOF {
		t.Error(err)
	}

	fmt.Println(user)
}
