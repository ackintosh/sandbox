package main

import (
	"log"
	"net/http"
)

func main() {
	http.HandleFunc("/", Hello)
	err := http.ListenAndServe(":8080", nil)
	if err != nil {
		panic(err)
	}
}

func Hello(w http.ResponseWriter, r *http.Request) {
	log.Printf("Hello. %s", r.Method)

	switch r.Method {
	case http.MethodGet:
		w.WriteHeader(200)
	default:
		w.WriteHeader(404)
	}
}
