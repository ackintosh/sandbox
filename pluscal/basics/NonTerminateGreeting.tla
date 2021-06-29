PlusCal options (-termination)
---- MODULE NonTerminateGreeting ----

\* 参考
\* https://hazm.at/mox/lang/tla+/pluscal/control-flow/index.html

\* ************************
\* *** 無限ループのサンプル ***
\* ************************
\* * InfiniteGreetingとは異なり、無限ループ(プログラムが停止しない経路, 非停止経路)を検出した場合にエラーになる
\*   Errors に `Temporal properties were violated.` が出る
\* * PlusCal では `--- MODULE ... ----` の前、または `===` の後、あるいはコメント部分に
\*   `PlusCal options (-termination)` と指定することでプログラムが停止しない経路を持つときにエラーとする TLA+ コードに変換することができる (ハイフンは省略可能)

EXTENDS TLC

(* --algorithm NonTerminateGreeting
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

\* BEGIN TRANSLATION (chksum(pcal) = "eed536e7" /\ chksum(tla) = "ad0fc78c")
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

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION 

====
