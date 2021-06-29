---- MODULE Transaction ----

\* 参考
\* https://hazm.at/mox/lang/tla+/pluscal/control-flow/index.html

\* ************************
\* *** Gotoのサンプル ***
\* ************************
\* 以下はデータをロックして読み込み、更新して書き込む、という手続きを失敗ケースも含めて記述し、
\* どのようなケースであっても最後にロックを解除していることを確認している

EXTENDS TLC

(* --algorithm Transaction
variables 
    lock = FALSE;
    case \in {"ReadFailure", "DataCannotUpdate", "WriteFailure", "Success"}
begin
    BeginTransaction:
        lock := TRUE;
        \* read user data...
        if case = "ReadFailure" then 
            print "failed to read user data.";
            goto EndTransaction;
        else 
            \* update and validate user data...
            if case = "DataCannotUpdate" then 
                print "data couldn't update.";
                goto EndTransaction;
            else 
                \* write user data...
                if case = "WriteFailure" then 
                    print "failed to write user data.";
                    goto EndTransaction;
                end if;
                Success:
                    print "The data has been updated.";
            end if;
        end if;
    EndTransaction:
        lock := FALSE;
    Finally:
        assert ~lock;
end algorithm; *)

\* BEGIN TRANSLATION (chksum(pcal) = "2c686d49" /\ chksum(tla) = "71792f99")
VARIABLES lock, case, pc

vars == << lock, case, pc >>

Init == (* Global variables *)
        /\ lock = FALSE
        /\ case \in {"ReadFailure", "DataCannotUpdate", "WriteFailure", "Success"}
        /\ pc = "BeginTransaction"

BeginTransaction == /\ pc = "BeginTransaction"
                    /\ lock' = TRUE
                    /\ IF case = "ReadFailure"
                          THEN /\ PrintT("failed to read user data.")
                               /\ pc' = "EndTransaction"
                          ELSE /\ IF case = "DataCannotUpdate"
                                     THEN /\ PrintT("data couldn't update.")
                                          /\ pc' = "EndTransaction"
                                     ELSE /\ IF case = "WriteFailure"
                                                THEN /\ PrintT("failed to write user data.")
                                                     /\ pc' = "EndTransaction"
                                                ELSE /\ pc' = "Success"
                    /\ case' = case

Success == /\ pc = "Success"
           /\ PrintT("The data has been updated.")
           /\ pc' = "EndTransaction"
           /\ UNCHANGED << lock, case >>

EndTransaction == /\ pc = "EndTransaction"
                  /\ lock' = FALSE
                  /\ pc' = "Finally"
                  /\ case' = case

Finally == /\ pc = "Finally"
           /\ Assert(~lock, "Failure of assertion at line 41, column 9.")
           /\ pc' = "Done"
           /\ UNCHANGED << lock, case >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == BeginTransaction \/ Success \/ EndTransaction \/ Finally
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

====
