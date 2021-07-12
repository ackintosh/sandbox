---- MODULE Dao ----

\* 参考
\* https://muratbuffalo.blogspot.com/2018/01/modeling-doa-attack-in-pluscal.html

EXTENDS Integers, Sequences, TLC
CONSTANT BALANCE, AMOUNT

(* --algorithm Dao
variables 
    attack = 3;
    bankBalance = BALANCE;
    malloryBalance = 0;

define
    SafeWithdrawal ==
        \/ bankBalance = BALANCE /\ malloryBalance = 0
        \/ bankBalance = BALANCE /\ malloryBalance = AMOUNT
        \/ bankBalance = BALANCE - AMOUNT /\ malloryBalance = AMOUNT
end define;

procedure BankWithdraw(amount)
begin
    CheckBalance:
        if bankBalance < amount then 
            return;
        end if;
    DispenseAmount:
        call MallorySendMoney(amount);
    FinishWithdraw:
        bankBalance := bankBalance - amount;
        return;
end procedure;

procedure MallorySendMoney(amount)
begin
    Receive:
        malloryBalance := malloryBalance + amount;
        if attack > 0 then 
            attack := attack - 1;
            call BankWithdraw(amount);
        end if;
    FC:
        return;
end procedure;

fair process Blockchain = "Blockchain"
begin
    Transact:
        call BankWithdraw(AMOUNT);
end process;

end algorithm; *)



\* BEGIN TRANSLATION (chksum(pcal) = "32362bfd" /\ chksum(tla) = "47741969")
\* Parameter amount of procedure BankWithdraw at line 22 col 24 changed to amount_
CONSTANT defaultInitValue
VARIABLES attack, bankBalance, malloryBalance, pc, stack

(* define statement *)
SafeWithdrawal ==
    \/ bankBalance = BALANCE /\ malloryBalance = 0
    \/ bankBalance = BALANCE /\ malloryBalance = AMOUNT
    \/ bankBalance = BALANCE - AMOUNT /\ malloryBalance = AMOUNT

VARIABLES amount_, amount

vars == << attack, bankBalance, malloryBalance, pc, stack, amount_, amount >>

ProcSet == {"Blockchain"}

Init == (* Global variables *)
        /\ attack = 3
        /\ bankBalance = BALANCE
        /\ malloryBalance = 0
        (* Procedure BankWithdraw *)
        /\ amount_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure MallorySendMoney *)
        /\ amount = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "Transact"]

CheckBalance(self) == /\ pc[self] = "CheckBalance"
                      /\ IF bankBalance < amount_[self]
                            THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                 /\ amount_' = [amount_ EXCEPT ![self] = Head(stack[self]).amount_]
                                 /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                            ELSE /\ pc' = [pc EXCEPT ![self] = "DispenseAmount"]
                                 /\ UNCHANGED << stack, amount_ >>
                      /\ UNCHANGED << attack, bankBalance, malloryBalance, 
                                      amount >>

DispenseAmount(self) == /\ pc[self] = "DispenseAmount"
                        /\ /\ amount' = [amount EXCEPT ![self] = amount_[self]]
                           /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "MallorySendMoney",
                                                                    pc        |->  "FinishWithdraw",
                                                                    amount    |->  amount[self] ] >>
                                                                \o stack[self]]
                        /\ pc' = [pc EXCEPT ![self] = "Receive"]
                        /\ UNCHANGED << attack, bankBalance, malloryBalance, 
                                        amount_ >>

FinishWithdraw(self) == /\ pc[self] = "FinishWithdraw"
                        /\ bankBalance' = bankBalance - amount_[self]
                        /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ amount_' = [amount_ EXCEPT ![self] = Head(stack[self]).amount_]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                        /\ UNCHANGED << attack, malloryBalance, amount >>

BankWithdraw(self) == CheckBalance(self) \/ DispenseAmount(self)
                         \/ FinishWithdraw(self)

Receive(self) == /\ pc[self] = "Receive"
                 /\ malloryBalance' = malloryBalance + amount[self]
                 /\ IF attack > 0
                       THEN /\ attack' = attack - 1
                            /\ /\ amount_' = [amount_ EXCEPT ![self] = amount[self]]
                               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "BankWithdraw",
                                                                        pc        |->  "FC",
                                                                        amount_   |->  amount_[self] ] >>
                                                                    \o stack[self]]
                            /\ pc' = [pc EXCEPT ![self] = "CheckBalance"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "FC"]
                            /\ UNCHANGED << attack, stack, amount_ >>
                 /\ UNCHANGED << bankBalance, amount >>

FC(self) == /\ pc[self] = "FC"
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ amount' = [amount EXCEPT ![self] = Head(stack[self]).amount]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << attack, bankBalance, malloryBalance, amount_ >>

MallorySendMoney(self) == Receive(self) \/ FC(self)

Transact == /\ pc["Blockchain"] = "Transact"
            /\ /\ amount_' = [amount_ EXCEPT !["Blockchain"] = AMOUNT]
               /\ stack' = [stack EXCEPT !["Blockchain"] = << [ procedure |->  "BankWithdraw",
                                                                pc        |->  "Done",
                                                                amount_   |->  amount_["Blockchain"] ] >>
                                                            \o stack["Blockchain"]]
            /\ pc' = [pc EXCEPT !["Blockchain"] = "CheckBalance"]
            /\ UNCHANGED << attack, bankBalance, malloryBalance, amount >>

Blockchain == Transact

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Blockchain
           \/ (\E self \in ProcSet:  \/ BankWithdraw(self)
                                     \/ MallorySendMoney(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ /\ WF_vars(Blockchain)
           /\ WF_vars(BankWithdraw("Blockchain"))
           /\ WF_vars(MallorySendMoney("Blockchain"))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

====
