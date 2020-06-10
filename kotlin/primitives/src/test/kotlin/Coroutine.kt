import kotlinx.coroutines.GlobalScope
import kotlinx.coroutines.delay
import kotlinx.coroutines.launch
import kotlinx.coroutines.runBlocking
import org.junit.jupiter.api.Nested
import org.junit.jupiter.api.Test

class Coroutine {
    // *バッドケース*
    // - 実行するコルーチンの終了するタイミングに気を配らなければならない
    // - メインスレッドを待機することで強引に辻褄をあわせてしまっている
    @Test
    fun badCase() {
        GlobalScope.launch {
            delay(1000L)
            println("World!")
        }

        println("Hello, ")
        Thread.sleep(2000L)
    }

    ////////////////////////////////////////////////////////////////////////
    // *構造化された並行性*
    // GlobalScopeでコルーチンを実行するのではなく、特定のスコープでコルーチンを実行すること
    ////////////////////////////////////////////////////////////////////////
    @Nested
    inner class StructuredConcurrency {

        // runBlockingコルーチンビルダ
        @Test
        fun runBlockingBuilder() = runBlocking {
            launch {
                delay(1000L)
                println("World!")
            }

            println("Hello, ")
        }
    }
}
