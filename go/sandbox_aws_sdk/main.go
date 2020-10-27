package main

import (
	"fmt"
	"github.com/aws/aws-sdk-go/service/dynamodb/dynamodbattribute"
)

func main() {
	var payload = make(map[string]string)
	payload["foo"] = "foovalue"
	payload["bar"] = "barvalue"
	payload["baz"] = ""

	m, err := dynamodbattribute.MarshalMap(payload)

	if err != nil {
		panic(err)
	}

	fmt.Println(m)
	// map[bar:{
	//    S: "barvalue"
	//  } baz:{
	//    NULL: true
	//  } foo:{
	//    S: "foovalue"
	// }]
}
