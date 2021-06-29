---- MODULE InfiniteGreeting ----

\* 参考
\* https://hazm.at/mox/lang/tla+/pluscal/control-flow/index.html

\* ************************
\* *** 無限ループのサンプル ***
\* ************************
\* * PlusCal はラベルで区別されるステップごとに状態変数を記録し、状態変数が過去に実行したときと完全に同一であればそれ以上の実行を省略する
\* * ラベル付けが必須の while 構文では 1 回のループごとに状態変数を確認し、過去の実行と同一の状態変数であることを検出したときに「無限ループとみなしてその経路の検証を停止する」
\* * 以下のサンプルでは停止条件がないため一見して無限に hello, world を出力し続けるように見えるが、1 回目のループとそれ以降のループで状態変数に変化がないことから、結果的に InfiniteGreeting ステップは 1 回しか実行されず、また次の Finally ステップは一度も実行されていないことが結果から分かる
\*   -> Coverageの Init と InfiniteGreeting が 1、それ以外は 0 になる
\* * 無限ループをエラーとしたい場合は、 NonTerminateGreeting.tla を参照

EXTENDS TLC

(* --algorithm InfiniteGreeting
variables 
    greeting = "hello, world";
begin
    \* while構文の先頭にはラベルを付けなければならない
    InfiniteGreeting:
        while TRUE do
            print greeting;
        end while;
    Finally:
        print "finished."
end algorithm; *)

\* BEGIN TRANSLATION (chksum(pcal) = "3667f629" /\ chksum(tla) = "89a66aff")
VARIABLES greeting, pc

vars == << greeting, pc >>

Init == (* Global variables *)
        /\ greeting = "hello, world"
        /\ pc = "InfiniteGreeting"

InfiniteGreeting == /\ pc = "InfiniteGreeting"
                    /\ PrintT(greeting)
                    /\ pc' = "InfiniteGreeting"
                    /\ UNCHANGED greeting

Finally == /\ pc = "Finally"
           /\ PrintT("finished.")
           /\ pc' = "Done"
           /\ UNCHANGED greeting

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == InfiniteGreeting \/ Finally
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

====
