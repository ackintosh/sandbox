---- MODULE StepProgress ----

\* 参考
\* https://hazm.at/mox/lang/tla+/pluscal/multi-process/index.html


EXTENDS Integers, TLC

(* --algorithm StepProgress
variables
    \* 各プロセス（プロセス1, 2）の状態を、タプル（要素数2）で管理する（ = 状態変数）
    locations = << 0, 0 >>

\* 単一プロセスのシステムでは begin から end algorithm の間に仕様を記述していたが、
\* マルチプロセスでは process ブロック内に同様の記述を行うことで並行システムを記述する
process Hopper \in 1..2
begin 
    Step1:
        locations[self] := 1;
        print locations;
    Step2:
        locations[self] := 2;
        print locations;
    Step3:
        locations[self] := 3;
        print locations;
end process;

\* システムの状態変数（ここでは locations）は、(0, 0)から始まり、すべてのプロセスが終了する時に (3, 3) に到達する
\* * プロセス数(n): 2
\* * 状態数(s): 4 (0から3)
\* より、s^n = 4^2 = 16
\* したがって、システムがとりうる状態の数は「16」

\* モデルのチェック結果（Output）
\* Output
\* <<1, 0>>
\* <<0, 1>>
\* <<2, 0>>
\* <<1, 1>> (2)
\* <<0, 2>>
\* <<3, 0>>
\* <<2, 1>> (2)
\* <<1, 2>> (2)
\* <<0, 3>>
\* <<3, 1>> (2)
\* <<2, 2>> (2)
\* <<1, 3>> (2)
\* <<3, 2>> (2)
\* <<2, 3>> (2)
\* <<3, 3>> (2)



end algorithm; *)

\* BEGIN TRANSLATION (chksum(pcal) = "f4790d81" /\ chksum(tla) = "e7ca22e8")
VARIABLES locations, pc

vars == << locations, pc >>

ProcSet == (1..2)

Init == (* Global variables *)
        /\ locations = << 0, 0 >>
        /\ pc = [self \in ProcSet |-> "Step1"]

Step1(self) == /\ pc[self] = "Step1"
               /\ locations' = [locations EXCEPT ![self] = 1]
               /\ PrintT(locations')
               /\ pc' = [pc EXCEPT ![self] = "Step2"]

Step2(self) == /\ pc[self] = "Step2"
               /\ locations' = [locations EXCEPT ![self] = 2]
               /\ PrintT(locations')
               /\ pc' = [pc EXCEPT ![self] = "Step3"]

Step3(self) == /\ pc[self] = "Step3"
               /\ locations' = [locations EXCEPT ![self] = 3]
               /\ PrintT(locations')
               /\ pc' = [pc EXCEPT ![self] = "Done"]

Hopper(self) == Step1(self) \/ Step2(self) \/ Step3(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in 1..2: Hopper(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

====
