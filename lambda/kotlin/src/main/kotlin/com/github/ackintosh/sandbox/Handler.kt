package com.github.ackintosh.sandbox

import com.amazonaws.services.lambda.runtime.Context
import com.amazonaws.services.lambda.runtime.RequestHandler
import com.amazonaws.services.lambda.runtime.events.SQSEvent

class Handler: RequestHandler<SQSEvent, Unit> {
    override fun handleRequest(input: SQSEvent, context: Context) {
        println("[hello from kotlin handler]")
        println("number of records: ${input.records.size}")

        for (r in input.records) {
            println("The message ${r.messageId} for event source ${r.eventSource} = ${r.body}")
            println("The length of body: ${r.body.toByteArray().size}")

            // 現在（ミリ秒）
            val now = System.currentTimeMillis()
            println("The message has been handled at: $now")

            // SentTimestamp: メッセージがキューに送られた時間（ミリ秒）
            // https://docs.aws.amazon.com/AWSSimpleQueueService/latest/APIReference/API_ReceiveMessage.html#API_ReceiveMessage_RequestParameters
            val sentTimestamp = r.attributes["SentTimestamp"]
            if (sentTimestamp != null) {
                println("SentTimestamp: $sentTimestamp")
                println("Elapsed time in millisecond: ${now - sentTimestamp.toLong()}")
            }
        }
    }
}
