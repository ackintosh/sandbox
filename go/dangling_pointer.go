package main

import "fmt"

// Handling Dangling Pointers in Go - Stack Overflow
// https://stackoverflow.com/questions/46987513/handling-dangling-pointers-in-go
func main() {
	var user = newUser("testuser")
	fmt.Print("test: %s", user.Name)
}

type User struct {
	Name string
}

// newUserでは関数内で作ったUserインスタンスへのポインタを返しているが、
// コンパイラが、関数のスコープを抜けた後もポインタが使われることを理解して、
// インスタンスをヒープに配置する
// なので、dangling pointerにならない

// Effective go
// https://golang.org/doc/effective_go.html#composite_literals
// Note that, unlike in C, it's perfectly OK to return the address of a local variable; the storage associated with the variable survives after the function returns.
func newUser(name string) *User {
	return &User{Name: name}
}
