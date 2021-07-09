---- MODULE InterProcessCommunication ----

\* 参考
\* https://hazm.at/mox/lang/tla+/pluscal/multi-process/index.html#interprocess-communication

EXTENDS TLC

\* ************************
\* *** プロセス間通信 ***
\* ************************
\* PlusCal のプロセスは互いを認識することができないため、プロセス間の通信はグローバルな状態変数を共有することで行われる
\* 別のプロセスによってグローバルな状態変数が期待する状態となるまで処理を待機する await を使用してプロセス間通信の同期ポイントを設置する

\* ************************
\* *** Echoサーバの例 ***
\* ************************
(* --algorithm InterProcessCommunication
variables
    \* プロセスは互いを認識できないためグローバルなスコープを持つ状態変数を用いて通信する必要がある
    \* Client - Server 間の通信は下記の2つの状態変数を使用する
    client_to_server = "";
    server_to_client = "";

process client = "Client"
begin 
    Send:
        client_to_server := "hello, world";
    Receive:
        \* *** await文 ***
        \* ラベル付けされたステップ中に await 文が含まれているとき、TLC はその条件式が true となるまでそのステップを実行対象から除外する (await の位置で停止するわけではない点に注意)
        \* これは別のプロセスが条件式を true とするような作用を起こすことを暗に期待しており、プロセス間の同期ポイントと考えることができる
        \* <注意>
        \* await 文はステップ中のどこでも配置することができるが、そのステップに入る前に条件式が false であった場合、「同一ステップ内で await より前に配置されている別の処理を実行しないまま停止する」
        \* この直観的ではない挙動がしばしば混乱を引き起こすため、可能な限りラベルの直後に await 文を配置することを推奨する
        await server_to_client /= "";
        print << "Client: ", server_to_client >>;
end process;

process server = "Server"
begin 
    Receive:
        await client_to_server /= "";
        print << "Server: ", client_to_server >>;
    Send:
        server_to_client := client_to_server;
end process;


end algorithm; *)

\* BEGIN TRANSLATION (chksum(pcal) = "71d99db5" /\ chksum(tla) = "fd42edfb")
\* Label Send of process client at line 16 col 9 changed to Send_
\* Label Receive of process client at line 18 col 9 changed to Receive_
VARIABLES client_to_server, server_to_client, pc

vars == << client_to_server, server_to_client, pc >>

ProcSet == {"Client"} \cup {"Server"}

Init == (* Global variables *)
        /\ client_to_server = ""
        /\ server_to_client = ""
        /\ pc = [self \in ProcSet |-> CASE self = "Client" -> "Send_"
                                        [] self = "Server" -> "Receive"]

Send_ == /\ pc["Client"] = "Send_"
         /\ client_to_server' = "hello, world"
         /\ pc' = [pc EXCEPT !["Client"] = "Receive_"]
         /\ UNCHANGED server_to_client

Receive_ == /\ pc["Client"] = "Receive_"
            /\ server_to_client /= ""
            /\ PrintT(<< "Client: ", server_to_client >>)
            /\ pc' = [pc EXCEPT !["Client"] = "Done"]
            /\ UNCHANGED << client_to_server, server_to_client >>

client == Send_ \/ Receive_

Receive == /\ pc["Server"] = "Receive"
           /\ client_to_server /= ""
           /\ PrintT(<< "Server: ", client_to_server >>)
           /\ pc' = [pc EXCEPT !["Server"] = "Send"]
           /\ UNCHANGED << client_to_server, server_to_client >>

Send == /\ pc["Server"] = "Send"
        /\ server_to_client' = client_to_server
        /\ pc' = [pc EXCEPT !["Server"] = "Done"]
        /\ UNCHANGED client_to_server

server == Receive \/ Send

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == client \/ server
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

====
