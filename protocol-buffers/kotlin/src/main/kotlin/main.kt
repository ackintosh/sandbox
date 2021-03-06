import com.github.ackintosh.proto.*
import com.google.protobuf.StringValue
import com.google.protobuf.Timestamp
import com.google.protobuf.util.JsonFormat
import com.google.rpc.BadRequest
import java.io.FileOutputStream

fun main() {
    ///////////////////////////////////////////////////////
    // シリアライズフォーマット(バイナリかJSONか)によって
    // サイズがどのくらい変化するのかを試してみる
    ///////////////////////////////////////////////////////

    // 項目数 3
    val smallItem = smallItem()
    // Protocol Buffersのバイナリフォーマットにシリアライズしたサイズ
    println(smallItem.serializedSize) // 27 bytes
    // JSONにシリアライズしたサイズ(bytes)
    println(JsonFormat.printer().print(smallItem).toByteArray().size) // 93 bytes

    // 項目数 22
    val item = item()
    // Protocol Buffersのバイナリフォーマットにシリアライズしたサイズ
    println(item.serializedSize) // 203 bytes
    // JSONにシリアライズしたサイズ(bytes)
    println(JsonFormat.printer().print(item).toByteArray().size) // 594 bytes

    // 項目数 205
    val bigItem = bigItem()
    // Protocol Buffersのバイナリフォーマットにシリアライズしたサイズ
    println(bigItem.serializedSize) // 2510 bytes
    // JSONにシリアライズしたサイズ(bytes)
    println(JsonFormat.printer().print(bigItem).toByteArray().size) // 5845 bytes

    errorDetails()

    oneOf()

    foo()

    wrapper()

    enum()

    optional()

//    writeTo()
}

fun smallItem() = SmallItem.newBuilder()
        .setString1("test string")
        .setNumber1(12345678)
        .setTimestamp1(
                Timestamp.newBuilder()
                        .setSeconds(System.currentTimeMillis() / 1000)
                        .setNanos(0)
        )
        .build()

fun item() = Item.newBuilder()
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

fun bigItem() = BigItem.newBuilder()
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
        .setString11("test string")
        .setString12("test string")
        .setString13("test string")
        .setString14("test string")
        .setString15("test string")
        .setString16("test string")
        .setString17("test string")
        .setString18("test string")
        .setString19("test string")
        .setString20("test string")
        .setString21("test string")
        .setString22("test string")
        .setString23("test string")
        .setString24("test string")
        .setString25("test string")
        .setString26("test string")
        .setString27("test string")
        .setString28("test string")
        .setString29("test string")
        .setString30("test string")
        .setString31("test string")
        .setString32("test string")
        .setString33("test string")
        .setString34("test string")
        .setString35("test string")
        .setString36("test string")
        .setString37("test string")
        .setString38("test string")
        .setString39("test string")
        .setString40("test string")
        .setString41("test string")
        .setString42("test string")
        .setString43("test string")
        .setString44("test string")
        .setString45("test string")
        .setString46("test string")
        .setString47("test string")
        .setString48("test string")
        .setString49("test string")
        .setString50("test string")
        .setString51("test string")
        .setString52("test string")
        .setString53("test string")
        .setString54("test string")
        .setString55("test string")
        .setString56("test string")
        .setString57("test string")
        .setString58("test string")
        .setString59("test string")
        .setString60("test string")
        .setString61("test string")
        .setString62("test string")
        .setString63("test string")
        .setString64("test string")
        .setString65("test string")
        .setString66("test string")
        .setString67("test string")
        .setString68("test string")
        .setString69("test string")
        .setString70("test string")
        .setString71("test string")
        .setString72("test string")
        .setString73("test string")
        .setString74("test string")
        .setString75("test string")
        .setString76("test string")
        .setString77("test string")
        .setString78("test string")
        .setString79("test string")
        .setString80("test string")
        .setString81("test string")
        .setString82("test string")
        .setString83("test string")
        .setString84("test string")
        .setString85("test string")
        .setString86("test string")
        .setString87("test string")
        .setString88("test string")
        .setString89("test string")
        .setString90("test string")
        .setString91("test string")
        .setString92("test string")
        .setString93("test string")
        .setString94("test string")
        .setString95("test string")
        .setString96("test string")
        .setString97("test string")
        .setString98("test string")
        .setString99("test string")
        .setString100("test string")
        .setString101("test string")
        .setString102("test string")
        .setString103("test string")
        .setString104("test string")
        .setString105("test string")
        .setString106("test string")
        .setString107("test string")
        .setString108("test string")
        .setString109("test string")
        .setString110("test string")
        .setString111("test string")
        .setString112("test string")
        .setString113("test string")
        .setString114("test string")
        .setString115("test string")
        .setString116("test string")
        .setString117("test string")
        .setString118("test string")
        .setString119("test string")
        .setString120("test string")
        .setString121("test string")
        .setString122("test string")
        .setString123("test string")
        .setString124("test string")
        .setString125("test string")
        .setString126("test string")
        .setString127("test string")
        .setString128("test string")
        .setString129("test string")
        .setString130("test string")
        .setString131("test string")
        .setString132("test string")
        .setString133("test string")
        .setString134("test string")
        .setString135("test string")
        .setString136("test string")
        .setString137("test string")
        .setString138("test string")
        .setString139("test string")
        .setString140("test string")
        .setString141("test string")
        .setString142("test string")
        .setString143("test string")
        .setString144("test string")
        .setString145("test string")
        .setString146("test string")
        .setString147("test string")
        .setString148("test string")
        .setString149("test string")
        .setString150("test string")
        .setString151("test string")
        .setString152("test string")
        .setString153("test string")
        .setString154("test string")
        .setString155("test string")
        .setString156("test string")
        .setString157("test string")
        .setString158("test string")
        .setString159("test string")
        .setString160("test string")
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
        .setNumber11(12345678)
        .setNumber12(12345678)
        .setNumber13(12345678)
        .setNumber14(12345678)
        .setNumber15(12345678)
        .setNumber16(12345678)
        .setNumber17(12345678)
        .setNumber18(12345678)
        .setNumber19(12345678)
        .setNumber20(12345678)
        .setNumber21(12345678)
        .setNumber22(12345678)
        .setNumber23(12345678)
        .setNumber24(12345678)
        .setNumber25(12345678)
        .setNumber26(12345678)
        .setNumber27(12345678)
        .setNumber28(12345678)
        .setNumber29(12345678)
        .setNumber30(12345678)
        .setNumber31(12345678)
        .setNumber32(12345678)
        .setNumber33(12345678)
        .setNumber34(12345678)
        .setNumber35(12345678)
        .setNumber36(12345678)
        .setNumber37(12345678)
        .setNumber38(12345678)
        .setNumber39(12345678)
        .setNumber40(12345678)
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
        .setTimestamp3(
            Timestamp.newBuilder()
                .setSeconds(System.currentTimeMillis() / 1000)
                .setNanos(0)
        )
        .setTimestamp4(
            Timestamp.newBuilder()
                .setSeconds(System.currentTimeMillis() / 1000)
                .setNanos(0)
        )
        .setTimestamp5(
            Timestamp.newBuilder()
                .setSeconds(System.currentTimeMillis() / 1000)
                .setNanos(0)
        )
        .build()

fun errorDetails() {
    val badRequest = BadRequest.newBuilder()
            .addFieldViolations(
                    BadRequest.FieldViolation.newBuilder()
                            .setField("invalid field 1")
                            .setDescription("xxx is invalid as the field")
                            .build()
            )
            .addFieldViolations(
                    BadRequest.FieldViolation.newBuilder()
                            .setField("invalid field 2")
                            .setDescription("xxx is invalid as the field")
                            .build()
            )
            .build()
    println(badRequest)
}

fun oneOf() {
    val m = OneOfMessage.newBuilder()
            .setNameA("name a")
            .setNameB("name b")
            .build()

    println(m.nameA)
    println(m.nameB)
    println(m.nameC)
    // name b
}

fun foo() {
    val foo = Foo.newBuilder().setName("test foo").setBar(Bar.newBuilder().setName("test bar")).build()

    println("foo ===========")
    println(foo)
    println(foo.hasBar())

    val foo2 = Foo.newBuilder().setName("test foo").build()
    println("foo2 ===========")
    println(foo2)
    println(foo2.hasBar())

    val bars = Bars.newBuilder().build()
    println("bars ===========")
    println(bars)
}

fun wrapper() {
        val string: String? = "test"
        val stringValue = StringValue.newBuilder().setValue(string).build()

        println(stringValue)

//        val stringNull: String? = null
//        val stringNullValue = StringValue.newBuilder().setValue(stringNull).build()
    // StringValue.setValue() で NPE が起きる

        println("usingWrapper ==========")
        val usingWrapper = UsingWrapper
                .newBuilder()
                .setStringProperty(StringValue.newBuilder().build())
                .build()

        println(usingWrapper.hasStringProperty())
        println(usingWrapper.stringProperty.value)

        val usingWrapper2 = UsingWrapper
                .newBuilder()
                .build()

        println(usingWrapper2.hasStringProperty())
        println(usingWrapper2.stringProperty.value)
}

fun enum() {
        val person = Person.newBuilder().setName("test person").build()
        println(person.name)
        println(person.favouriteSeason)

        val anotherPerson = Person.newBuilder().setName("another person").setFavouriteSeason(Season.forNumber(100))
        println(anotherPerson.name)
        println(anotherPerson.favouriteSeason)

        val status = Status.UNKNOWN
        println(status)

        val m1 = AwesomeMessage1
                .newBuilder()
                .setStatus(AwesomeMessage1.Status.UNKNOWN)
                .build()
        println(m1)

        val m2 = AwesomeMessage2
                .newBuilder()
                .setStatus(AwesomeMessage2.Status.UNKNOWN)
                .build()
        println(m2)
}

// https://github.com/protocolbuffers/protobuf/blob/master/docs/field_presence.md
fun optional() {
        val person = OptionalPerson.newBuilder().setName("test person").build()
        println(person.name)
        println(person.favouriteSeason)

        // hasメソッドで有無を確認できる
        println("person.hasMiddleName: ${person.hasMiddleName()}")
        println("person.hasFavouriteSeason: ${person.hasFavouriteSeason()}")
        // セットされていない場合、値はデフォルト値
        println("person.MiddleName: ${person.middleName}") // 空文字
        println("person.FavouriteSeason: ${person.favouriteSeason}") // 0番目の要素(SEASON_UNKNOWN)

        val person2 = OptionalPerson.newBuilder()
                .setName("test person")
                .setMiddleName("test middle name")
                .build()

        println("person2.hasMiddleName: ${person2.hasMiddleName()}")
        println("personn2.MiddleName: ${person2.middleName}")
}

// ファイルに書き出す
fun writeTo() {
    val smallItem = smallItem()
    val output = FileOutputStream("./output.bin")
    smallItem.writeTo(output)
}
