---- MODULE ReadPassword ----

\* 参考
\* https://hazm.at/mox/lang/tla+/pluscal/control-flow/index.html

\* *************************
\* *** while構文のサンプル ***
\* *************************
\* 正しいパスワードを入力するまで最大 3 回の試行を繰り返す処理を行っている

EXTENDS Integers, TLC

(* --algorithm ReadPassword
variables 
    max_retry = 3;
    correct_password = "success!";
    retry = 0;
    input = "";
begin
    \* while構文の先頭にはラベルを付けなければならない
    ReadPassword:
        while input /= correct_password /\ retry < max_retry do
            either
                input := "success!";
            or
                input := "failure?";
            end either;
            retry := retry + 1;
        end while;
    Finally:
        assert input = correct_password \/ retry = max_retry;
        print << retry, input >>
end algorithm; *)

\* BEGIN TRANSLATION (chksum(pcal) = "ec3a379e" /\ chksum(tla) = "f4732446")
VARIABLES max_retry, correct_password, retry, input, pc

vars == << max_retry, correct_password, retry, input, pc >>

Init == (* Global variables *)
        /\ max_retry = 3
        /\ correct_password = "success!"
        /\ retry = 0
        /\ input = ""
        /\ pc = "ReadPassword"

ReadPassword == /\ pc = "ReadPassword"
                /\ IF input /= correct_password /\ retry < max_retry
                      THEN /\ \/ /\ input' = "success!"
                              \/ /\ input' = "failure?"
                           /\ retry' = retry + 1
                           /\ pc' = "ReadPassword"
                      ELSE /\ pc' = "Finally"
                           /\ UNCHANGED << retry, input >>
                /\ UNCHANGED << max_retry, correct_password >>

Finally == /\ pc = "Finally"
           /\ Assert(input = correct_password \/ retry = max_retry, 
                     "Failure of assertion at line 29, column 9.")
           /\ PrintT(<< retry, input >>)
           /\ pc' = "Done"
           /\ UNCHANGED << max_retry, correct_password, retry, input >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == ReadPassword \/ Finally
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

====
