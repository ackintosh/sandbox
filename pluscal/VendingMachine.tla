---- MODULE VendingMachine ----

\* 参考
\* https://hazm.at/mox/lang/tla+/pluscal/control-flow/index.html

\* ************************
\* *** eitherのサンプル ***
\* ************************
\* either はシステムが取りうる非決定性挙動の分岐を記述する
\* 以下の自動販売機の例では、コインを入れた利用者がタバコかスナックかまたは返却を選択する動作を either を使って表現している

\* 実行結果に注目すると、最初の PutCoin ステップは 1 回しか実行されていないにも関わらず either を内包する ChooseProduct ステップは 3 回実行されていることが分かる
\* これは PlusCal が非決定性挙動を認識して自動的に 1) タバコを購入するケース、2) スナックを購入するケース、3) コインを返却するという 3 つの経路を検証するためである

\* while と either を組み合わせた複雑な経路の検証は ReadPassword.tla を参照

EXTENDS Integers, TLC

(* --algorithm VendingMachine
variables 
    revenue = 0;
    deposite = 0;
    dispensing_slot = "";
begin
    PutCoin:
        deposite := 1;
    ChooseProduct:
        either
            Cigarette:
                dispensing_slot := "Cigarette";
                revenue := revenue + deposite;
                deposite := 0;
        or
            Snack:
                dispensing_slot := "Mixed Nuts";
                revenue := revenue + deposite;
                deposite := 0;
        or
            ToReturnCoin:
                dispensing_slot := "Coin";
                deposite := 0;
        end either;
    Finally:
        assert deposite = 0;
        assert (dispensing_slot = "Coin" /\ revenue = 0) \/ revenue = 1;
        print dispensing_slot;
end algorithm; *)

\* BEGIN TRANSLATION (chksum(pcal) = "fdeb6546" /\ chksum(tla) = "5551236")
VARIABLES revenue, deposite, dispensing_slot, pc

vars == << revenue, deposite, dispensing_slot, pc >>

Init == (* Global variables *)
        /\ revenue = 0
        /\ deposite = 0
        /\ dispensing_slot = ""
        /\ pc = "PutCoin"

PutCoin == /\ pc = "PutCoin"
           /\ deposite' = 1
           /\ pc' = "ChooseProduct"
           /\ UNCHANGED << revenue, dispensing_slot >>

ChooseProduct == /\ pc = "ChooseProduct"
                 /\ \/ /\ pc' = "Cigarette"
                    \/ /\ pc' = "Snack"
                    \/ /\ pc' = "ToReturnCoin"
                 /\ UNCHANGED << revenue, deposite, dispensing_slot >>

Cigarette == /\ pc = "Cigarette"
             /\ dispensing_slot' = "Cigarette"
             /\ revenue' = revenue + deposite
             /\ deposite' = 0
             /\ pc' = "Finally"

Snack == /\ pc = "Snack"
         /\ dispensing_slot' = "Mixed Nuts"
         /\ revenue' = revenue + deposite
         /\ deposite' = 0
         /\ pc' = "Finally"

ToReturnCoin == /\ pc = "ToReturnCoin"
                /\ dispensing_slot' = "Coin"
                /\ deposite' = 0
                /\ pc' = "Finally"
                /\ UNCHANGED revenue

Finally == /\ pc = "Finally"
           /\ Assert(deposite = 0, 
                     "Failure of assertion at line 39, column 9.")
           /\ Assert((dispensing_slot = "Coin" /\ revenue = 0) \/ revenue = 1, 
                     "Failure of assertion at line 40, column 9.")
           /\ PrintT(dispensing_slot)
           /\ pc' = "Done"
           /\ UNCHANGED << revenue, deposite, dispensing_slot >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == PutCoin \/ ChooseProduct \/ Cigarette \/ Snack \/ ToReturnCoin
           \/ Finally
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

====
