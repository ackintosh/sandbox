// # 参考URL
// * https://codezine.jp/article/detail/60

// DIを使わない場合
fun notDI() {
    class B

    // クラスAはクラスBのサービスを利用している
    class A {
        // * クラスAの内部でクラスBをインスタンス化している
        // * Bを修正する場合(例えばコンストラクタの引数を追加する場合)にAの修正も必要になってしまうため、クラス間の結び付きが強くなってしまっている
        private val b = B()
    }

    val a = A()
}

// DIを使う
fun di() {
    class B

    class A(val b: B)

    // * Bのインスタンスを生成する責任を、AからIoCに移る
    //   -> インスタンスの生成方法をIoCが管理する
    //     -> DIが、クラスAのコンストラクタに必要な引数を渡してくれる( = Dependency Injection)
    class DI {
        fun getA() = A(getB())
        fun getB() = B()
    }

    val a = DI().getA()
}
