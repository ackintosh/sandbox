import com.fasterxml.jackson.annotation.JsonProperty
import com.fasterxml.jackson.module.kotlin.jacksonObjectMapper
import com.fasterxml.jackson.module.kotlin.readValue
import java.time.Instant
import java.util.*
import kotlin.properties.Delegates

fun main() {
    val json = "{ \"name\": \"bob\", \"age\":20 }"
    val mapper = jacksonObjectMapper()

    // *JSON から Object へ*
    val state = mapper.readValue<MyStateObject>(json)
    println(state)
    // MyStateObject(name=bob, age=20)

    // *Object から JSON へ*
    println(mapper.writeValueAsString(state))
    // {"name":"bob","age":20}

    // ========= アノテーション ===========
    val annotatedState = mapper.readValue<MyAnnotatedStateObject>(json)
    println(annotatedState)
    // MyAnnotatedStateObject(foo=bob, bar=20)

    // ========= JSONで渡されないフィールドを後で入れる場合 ===========
    val stateObjectWithPartialFieldsInConstructor = mapper.readValue<StateObjectWithPartialFieldsInConstructor>("{ \"name\": \"bob\", \"age\":20 }")
    // `lateinit` や `Delegates.notNull()` のフィールドが null なので、
    // JSONに書き出そうとしてもエラーになる
    // println(mapper.writeValueAsString(stateObjectWithPartialFieldsInConstructor))

    stateObjectWithPartialFieldsInConstructor.primaryAddress = "東京都"
    stateObjectWithPartialFieldsInConstructor.createdAt = Date.from(Instant.now())
    println(mapper.writeValueAsString(stateObjectWithPartialFieldsInConstructor))
    // {"name":"bob","age":20,"createdAt":1581312657334,"address":"東京都"}
}

data class MyStateObject(
    val name: String,
    val age: Int
)

// @JsonPropertyでJSONのフィールドとdataクラスのフィールドの対応付けを定義する
data class MyAnnotatedStateObject(
    @JsonProperty("name") val foo: String,
    @JsonProperty("age") val bar: Int
)

data class StateObjectWithPartialFieldsInConstructor(
    val name: String,
    @JsonProperty("age") val years: Int
) {
    // `lateinit` や `Delegates.notNull()` は、そのフィールドにアクセスした時にnullじゃないことを保証してくれる
    @JsonProperty("address") lateinit var primaryAddress: String // JSONに書き出すときはフィールド名が "address" になる
    var createdAt: Date by Delegates.notNull()
}
