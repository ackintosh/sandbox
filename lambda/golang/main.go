package main

import (
    "context"
    "fmt"
    "time"

    "github.com/aws/aws-lambda-go/events"
    "github.com/aws/aws-lambda-go/lambda"
)

func handler(ctx context.Context, sqsEvent events.SQSEvent) error {
    for _, message := range sqsEvent.Records {
        fmt.Printf("The message %s for event source %s = %s \n", message.MessageId, message.EventSource, message.Body)
        fmt.Printf("Attributes: %s \n", message.Attributes)

        // SentTimestamp: メッセージがキューに送られた時間（ミリ秒）
        // https://docs.aws.amazon.com/AWSSimpleQueueService/latest/APIReference/API_ReceiveMessage.html#API_ReceiveMessage_RequestParameters
        fmt.Printf("SentTimestamp: %s \n", message.Attributes["SentTimestamp"])

        // 現在（ミリ秒）
        fmt.Printf("The message has been handled at: %d \n", time.Now().UnixNano() / int64(time.Millisecond))
    }

    return nil
}

func main() {
    lambda.Start(handler)
}
