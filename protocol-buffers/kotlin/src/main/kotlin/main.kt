import com.github.ackintosh.proto.Item
import com.google.protobuf.Timestamp
import com.google.protobuf.util.JsonFormat

fun main() {
    ///////////////////////////////////////////////////////
    // シリアライズフォーマット(バイナリかJSONか)によって
    // サイズがどのくらい変化するのかを試してみる
    ///////////////////////////////////////////////////////
    val item = Item.newBuilder()
        .setString1("test string")
        .setString2("test string")
        .setString3("test string")
        .setString4("test string")
        .setString5("test string")
        .setString6("test string")
        .setString7("test string")
        .setString8("test string")
        .setString9("test string")
        .setString10("test string")
        .setNumber1(12345678)
        .setNumber2(12345678)
        .setNumber3(12345678)
        .setNumber4(12345678)
        .setNumber5(12345678)
        .setNumber6(12345678)
        .setNumber7(12345678)
        .setNumber8(12345678)
        .setNumber9(12345678)
        .setNumber10(12345678)
        .setTimestamp1(
            Timestamp.newBuilder()
                .setSeconds(System.currentTimeMillis() / 1000)
                .setNanos(0)
        )
        .setTimestamp2(
            Timestamp.newBuilder()
                .setSeconds(System.currentTimeMillis() / 1000)
                .setNanos(0)
        )
        .build()

    println(item)

    // Protocol Buffersのバイナリフォーマットにシリアライズしたサイズ(bytes)
    println(item.serializedSize) // 203 bytes

    // JSONにシリアライズしたサイズ(bytes)
    println(JsonFormat.printer().print(item).toByteArray().size) // 594 bytes

}
