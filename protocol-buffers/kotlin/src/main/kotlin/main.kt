import com.github.ackintosh.proto.Item
import com.google.protobuf.Timestamp

fun main() {
    val item = Item.newBuilder()
        .setItemCode("test item")
        .setPrice(100)
        .setSize(10)
        .setWeight(50)
        .setReleaseDate(
            Timestamp.newBuilder()
                .setSeconds(System.currentTimeMillis())
                .setNanos(0)
        )
        .build()
    println(item)
}