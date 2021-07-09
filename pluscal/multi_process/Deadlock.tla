---- MODULE Deadlock ----

\* 参考
\* https://hazm.at/mox/lang/tla+/pluscal/multi-process/index.html#deadlock

EXTENDS TLC

\* ************************
\* *** デッドロック ***
\* ************************
\* デッドロック (deadlock) はどのプロセスもステップを進行することができなくなったときに TLC により Deadlock reached というメッセージで報告されるエラー
\* PlusCal のマルチプロセス環境では await で待機しているプロセスがいるにもかかわらず他にステップを進めることのできるプロセスが存在しなくなったときに発生する
\* また TLA+ を使っているケースでは単一プロセスの場合であっても Next で次に実行可能なステップが存在しなかったときに発生する

\* デッドロックをシステムの正常停止と定義するようなシステムを検証する場合は
\* cfgファイルに "CHECK_DEADLOCK FALSE" を追加することで TLC がデッドロックをエラーとして扱わないようになる

(* --algorithm Deadlock
variables
    \* プロセス間通信のために使う状態変数
    client_to_server = "";
    server_to_client = "";

\* Client, Serverそれぞれが相手の通信待ち(await)になり、デッドロックが発生する
process client = "Client"
begin 
    Receive:
        await server_to_client /= "";
        print << "Client: ", server_to_client >>;
end process;

process server = "Server"
begin 
    Receive:
        await client_to_server /= "";
        print << "Server: ", client_to_server >>;
end process;


end algorithm; *)

\* BEGIN TRANSLATION (chksum(pcal) = "b0a32322" /\ chksum(tla) = "2c6c4e2f")
\* Label Receive of process client at line 20 col 9 changed to Receive_
VARIABLES client_to_server, server_to_client, pc

vars == << client_to_server, server_to_client, pc >>

ProcSet == {"Client"} \cup {"Server"}

Init == (* Global variables *)
        /\ client_to_server = ""
        /\ server_to_client = ""
        /\ pc = [self \in ProcSet |-> CASE self = "Client" -> "Receive_"
                                        [] self = "Server" -> "Receive"]

Receive_ == /\ pc["Client"] = "Receive_"
            /\ server_to_client /= ""
            /\ PrintT(<< "Client: ", server_to_client >>)
            /\ pc' = [pc EXCEPT !["Client"] = "Done"]
            /\ UNCHANGED << client_to_server, server_to_client >>

client == Receive_

Receive == /\ pc["Server"] = "Receive"
           /\ client_to_server /= ""
           /\ PrintT(<< "Server: ", client_to_server >>)
           /\ pc' = [pc EXCEPT !["Server"] = "Done"]
           /\ UNCHANGED << client_to_server, server_to_client >>

server == Receive

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == client \/ server
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

====
