---- MODULE FizzBuzz ----

EXTENDS Integers, Sequences, TLC

(* --algorithm FizzBuzz
variables 
    number \in 1..20;
    answer = "";

begin
    FizzBuzz:
        if number % 3 = 0 /\ number % 5 = 0 then 
            answer := "Fizz Buzz";
        elsif number % 3 = 0 then 
            answer := "Fizz";
        elsif number % 5 = 0 then 
            answer := "Buzz";
        else 
            answer := ToString(number);
        end if;
    Finally:
        assert
            \/ /\ answer = "Fizz" /\ number % 3 = 0 /\ number % 5 /= 0
            \/ /\ answer = "Buzz" /\ number % 3 /= 0 /\ number % 5 = 0
            \/ /\ answer = "Fizz Buzz" /\ number % 3 = 0 /\ number % 5 = 0
            \/ /\ answer /= "Fizz" /\ answer /= "Buzz" /\ answer /= "FizzBuzz" /\ number % 3 /= 0 /\ number % 5 /= 0;
        print answer;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "8d38478" /\ chksum(tla) = "bcc8c8c3")
VARIABLES number, answer, pc

vars == << number, answer, pc >>

Init == (* Global variables *)
        /\ number \in 1..20
        /\ answer = ""
        /\ pc = "FizzBuzz"

FizzBuzz == /\ pc = "FizzBuzz"
            /\ IF number % 3 = 0 /\ number % 5 = 0
                  THEN /\ answer' = "Fizz Buzz"
                  ELSE /\ IF number % 3 = 0
                             THEN /\ answer' = "Fizz"
                             ELSE /\ IF number % 5 = 0
                                        THEN /\ answer' = "Buzz"
                                        ELSE /\ answer' = ToString(number)
            /\ pc' = "Finally"
            /\ UNCHANGED number

Finally == /\ pc = "Finally"
           /\ Assert(\/ /\ answer = "Fizz" /\ number % 3 = 0 /\ number % 5 /= 0
                     \/ /\ answer = "Buzz" /\ number % 3 /= 0 /\ number % 5 = 0
                     \/ /\ answer = "Fizz Buzz" /\ number % 3 = 0 /\ number % 5 = 0
                     \/ /\ answer /= "Fizz" /\ answer /= "Buzz" /\ answer /= "FizzBuzz" /\ number % 3 /= 0 /\ number % 5 /= 0, 
                     "Failure of assertion at line 22, column 9.")
           /\ PrintT(answer)
           /\ pc' = "Done"
           /\ UNCHANGED << number, answer >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == FizzBuzz \/ Finally
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

====
