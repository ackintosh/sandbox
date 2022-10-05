package main

import (
	"context"
	"fmt"
	"github.com/aws/aws-lambda-go/events"
	"github.com/aws/aws-lambda-go/lambda"
)

func main() {
	lambda.Start(handler)
}

// cf. https://github.com/aws/aws-lambda-go/blob/main/events/README_Kinesis.md
func handler(ctx context.Context, kinesisEvent events.KinesisEvent) {
	fmt.Println("Hello!")

	for _, record := range kinesisEvent.Records {
		kinesisRecord := record.Kinesis
		dataBytes := kinesisRecord.Data
		dataText := string(dataBytes)

		fmt.Printf("%s Data = %s \n", record.EventName, dataText)
	}
}
