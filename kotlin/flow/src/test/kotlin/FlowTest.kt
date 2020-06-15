import kotlinx.coroutines.*
import kotlinx.coroutines.flow.Flow
import kotlinx.coroutines.flow.collect
import kotlinx.coroutines.flow.flow
import org.junit.jupiter.api.Test

class FlowTest {
    @Test
    fun example() = runBlocking {
        launch {
            for (k in 1..3) {
                println("I'm not blocked $k")
                delay(100)
            }
        }

        flowBuilder().collect { value -> println(value) }
        // I'm not blocked 1
        // 1
        // I'm not blocked 2
        // 2
        // I'm not blocked 3
        // 3
    }

    fun flowBuilder(): Flow<Int> = flow {
        for (i in 1..3) {
            delay(100)
            emit(i)
        }
    }
}