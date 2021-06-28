---- MODULE HelloWorld ----
\* モジュール名
\* ファイル名の [モジュール名].tla と TLA+ 構文の MODULE [モジュール名] でモジュール名を同じにしなければならない
\* ただし PlusCal 構文の algorithm [アルゴリズム名] はモジュール名とは異なる名前にしても良い

\* 実行方法(VSCode)
\* 1. Cmd + Ctrl + P で表示されるパネルで「TLA+:Parse module」を実行する
\* 2. すると コードに "BEGIN TRANSLATION" ～ "END TRANSLATION" が挿入される
\* 3. ソースを右クリックで "Check model with TLC" を選択する

\* PlusCalのコードからTLA+の機能を使うときはTLA+の構文で EXTENDS を指定する
\* この例では HelloWorld モジュール内で print という機能を使用するために TLC モジュールをEXTENDしている
\* 標準で使用できるモジュールとその機能については下記URLを参照
\* https://github.com/tlaplus/tlaplus/tree/master/tlatools/org.lamport.tlatools/src/tla2sany/StandardModules
EXTENDS TLC

\* PlusCal の構文は algorithm [モジュール名] から end algorithm; までの間で、それより外は TLA+ の構文
(* --algorithm HelloWorld
begin
    Greeting:
        print "hello, world";
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "8124a86e" /\ chksum(tla) = "56880286")
VARIABLE pc

vars == << pc >>

Init == /\ pc = "Greeting"

Greeting == /\ pc = "Greeting"
            /\ PrintT("hello, world")
            /\ pc' = "Done"

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Greeting
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

====
