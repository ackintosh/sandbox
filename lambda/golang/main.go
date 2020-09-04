package main

import (
	"context"
	"fmt"
	"strconv"
	"time"

	"github.com/aws/aws-lambda-go/events"
	"github.com/aws/aws-lambda-go/lambda"
)

func handler(ctx context.Context, sqsEvent events.SQSEvent) error {
	for _, message := range sqsEvent.Records {
		fmt.Printf("The message %s for event source %s = %s \n", message.MessageId, message.EventSource, message.Body)
		fmt.Printf("Attributes: %s \n", message.Attributes)

		// 現在（ミリ秒）
		var now = time.Now().UnixNano() / int64(time.Millisecond)
		fmt.Printf("The message has been handled at: %d \n", now)

		// SentTimestamp: メッセージがキューに送られた時間（ミリ秒）
		// https://docs.aws.amazon.com/AWSSimpleQueueService/latest/APIReference/API_ReceiveMessage.html#API_ReceiveMessage_RequestParameters
		var sentTimestamp, err = strconv.ParseInt(message.Attributes["SentTimestamp"], 10, 64)
		if err != nil {
			panic("failed to convert SetTimestamp")
		}
		fmt.Printf("SentTimestamp: %d \n", sentTimestamp)

		fmt.Printf("Elapsed time in millisecond: %d \n", now-sentTimestamp)
	}

	return nil
}

func main() {
	lambda.Start(handler)
}
