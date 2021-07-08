import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test
import java.math.BigDecimal
import java.time.Clock
import java.time.LocalDateTime
import java.time.ZoneId

class MainTest {
    // Effective Java 第3版
    // 項目60 正確な答えが必要ならば、floatとdoubleを避ける
    // * float型とdouble型は、とりわけ金銭計算には適していない
    // * なぜなら、floatあるいはdoubleを使って正確に 0.1 (あるいは他の10のマイナス乗)を表現することは不可能
    @Test
    fun test1() {
        //////////////////////////
        // 例1
        //////////////////////////
        val ex1 = 1.03 - 0.42
        // 0.61にはならない
        Assertions.assertEquals(0.6100000000000001, ex1)

        //////////////////////////
        // 例2
        //////////////////////////
        val ex2 = 1.00 - (9 * 0.1)
        // 0.1にはならない
        Assertions.assertEquals(0.09999999999999998, ex2)
    }

    // 正しくは、BigDecimal, int, long を使う
    // BigDecimalを使うデメリット
    // * float, doubleを使うのと比べると、処理が遅い・不便
    @Test
    fun test2() {
        val ex1 = BigDecimal.valueOf(1.03).subtract(BigDecimal.valueOf(0.42))
        // 0.61になる
        Assertions.assertEquals(BigDecimal.valueOf(0.61), ex1)



        // TEST
        val dateTime = LocalDateTime.now()
        println(dateTime)

        val clock = Clock.system(ZoneId.of("Asia/Tokyo"))
        val anotherDateTime = LocalDateTime.now(clock)
        println(anotherDateTime)

        Assertions.assertEquals(dateTime.year, anotherDateTime.year)
        Assertions.assertEquals(dateTime.month, anotherDateTime.month)
        Assertions.assertEquals(dateTime.dayOfMonth, anotherDateTime.dayOfMonth)
        Assertions.assertEquals(dateTime.hour, anotherDateTime.hour)
        Assertions.assertEquals(dateTime.minute, anotherDateTime.minute)
    }
}
