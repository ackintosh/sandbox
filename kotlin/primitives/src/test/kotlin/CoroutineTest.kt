import kotlinx.coroutines.*
import org.junit.jupiter.api.Nested
import org.junit.jupiter.api.Test

class CoroutineTest {
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
        Thread.sleep(2000L) // ここをコメントアウトすると "Hello," だけ出力してプログラムが終了してしまう
    }

    ////////////////////////////////////////////////////////////////////////
    // *構造化された並行性*
    // GlobalScopeでコルーチンを実行するのではなく、特定のスコープでコルーチンを実行すること
    ////////////////////////////////////////////////////////////////////////
    @Nested
    inner class StructuredConcurrency {

        // 構造化1: runBlockingコルーチンビルダ
        // runBlockingを含むすべてのコルーチンビルダは、そのコードブロックのレシーバが CoroutineScope になっている
        @Test
        fun runBlockingBuilder() = runBlocking {
            // 外側のコルーチン(ここではrunBlocking)は、そのスコープで起動されたすべてのコルーチンが完了するまで
            // 完了しないので、明示的に結合することなく、このスコープでコルーチンを起動できる
            launch {
                delay(1000L)
                println("World!")
            }

            println("Hello, ")
        }

        // 構造化2: スコープビルダを使って独自のスコープを作る
        // coroutineScopeビルだはコルーチンスコープを作成し、スコープ内で起動したすべてのコルーチンが完了するまで待機する
        @Test
        fun scopeBuilder() = runBlocking {
            // coroutineScopeビルダで作ったスコープ内で起動したすべてのコルーチンが完了するまで待機する
            coroutineScope {
                launch {
                    delay(1000L)
                    println("Hello,")
                }
            }

            // 処理が次のステートメントに移ったときには、coroutineScopeの中身がすべて完了していることが保証される
            println("World!!")
        }
    }
}
