------------------------- MODULE broadcast_prepare -------------------------
\* This is a broadcast protocol
\* Capable of handling an arbitrary number of replicas, with a client who sends the initial message to an arbitrary "selected" leader replica
\* Chosen leader replica sends a message "m1" to all replicas besides itself, the replicas receive the message and remove it from the sent_queue
\* **All replicas who receive a message, send message to all other replicas**
\* ///TODO Replicas all send message back to the client

EXTENDS Integers, Sequences, TLC
CONSTANT replicaSet, chosenLeader

(* --algorithm echo

variables
clientRequest = "";
lastSent = "";
replicaTermination_preprep = [r \in replicaSet |-> FALSE];
replicaTermination_prepare = [r \in replicaSet |-> FALSE];
replicaTermination_commit = [r \in replicaSet |-> FALSE];
replicaTermination = [r \in replicaSet |-> FALSE];
serverTerminated = FALSE;
\*chosenLeader = "c1"; \* Implement leader lock later
sent_queue = <<>>;
sender = "";
sentTo = "";
messageSet = {"m1"};
globalSeqNum = 0;
msg_struct = [m |-> "", sender |-> "", to |-> "", seq |-> 0, type |-> ""];


define
    MessageTypes == {"preprepare", "prepare", "commit", "client_request", "client_response"}
    ReplicaOrClient == replicaSet \cup {"client"}
    MessageSet == {"m1"}
    
    TypeOK ==
        /\ sent_queue \in Seq([type: MessageTypes, 
                               sender: ReplicaOrClient, 
                               to: ReplicaOrClient,
                               m: MessageSet, 
                               seq: 1..100])
        /\ globalSeqNum \in Nat
        /\ replicaTermination_preprep \in [replicaSet -> BOOLEAN]
        /\ replicaTermination_prepare \in [replicaSet -> BOOLEAN]
        
    StateConstraint ==
    /\ globalSeqNum <= 3
    /\ Len(sent_queue) <= 5
    
    TerminationCorrectness == <>(\A r \in replicaSet : replicaTermination[r])
    

end define;

procedure Broadcast(from, msg, type)
variables
toSend = replicaSet \ {from};
begin
    BroadcastLoop:
        while toSend # {} do
            with r \in toSend do
                globalSeqNum := globalSeqNum + 1;
                msg_struct := [m |-> msg, sender |-> from, to |-> r, seq |-> globalSeqNum, type |-> type];
                sent_queue := Append(sent_queue, msg_struct);
                toSend := toSend \ {r};
                print <<"Replica " \o self \o " sent " \o msg_struct.m \o " to " \o r \o ". Seq# -> " \o ToString(globalSeqNum) \o " | Type = " \o type>>;
            end with;
        end while;
    return;
end procedure;


process Replica \in replicaSet
variables
\*sending \in messageSet;
message = "";
preprep_received = ""; \* Maybe hold entire struct
prepare_received = ""; \* Maybe hold entire struct
commit_received = ""; \* Maybe hold entire struct
toSend = {};
replicaID = self;
client = "";
\* local memory for last sent
begin
    PrimarySends:
        if (chosenLeader = {self}) then
            await (sent_queue # <<>> /\ Head(sent_queue).to = self);
            message := Head(sent_queue).m;
            client := Head(sent_queue).sender;
            sent_queue := Tail(sent_queue);
            DoBroadcast:
                call Broadcast(self, message, "preprepare");
            SetPrePrepareMessage:
                preprep_received := message;
                replicaTermination_preprep[self] := TRUE;
\*        end if;
        else
    WaitForPrePrepare:
        await (sent_queue # <<>> /\ Head(sent_queue).to = self /\ Head(sent_queue).type = "preprepare");
        preprep_received := Head(sent_queue).m;
        sent_queue := Tail(sent_queue);
        print <<"Sent Queue now: " \o ToString(Len(sent_queue))>>;
        replicaTermination_preprep[self] := TRUE;
        end if;
    SendPrepare:
        if (replicaTermination_preprep[self]) then
            DoPrepareBroadcast:
                print <<"BROADCASTING PREPARE">>;
                call Broadcast(self, preprep_received, "prepare");
        end if;      
    WaitForPrepare:
        await (sent_queue # <<>> /\ Head(sent_queue).to = self /\ Head(sent_queue).type = "prepare");
        prepare_received := Head(sent_queue).m;
        sent_queue := Tail(sent_queue);
        print <<"GETTING READY TO CAST COMMIT">>;
        replicaTermination_prepare[self] := TRUE;
    SendCommit:
        if (replicaTermination_prepare[self]) then
            DoCommitBroadcast:
                print <<"BROADCASTING COMMIT">>;
                call Broadcast(self, prepare_received, "commit");
        end if;
    WaitForCommit:
        await (sent_queue # <<>> /\ Head(sent_queue).to = self /\ Head(sent_queue).type = "commit");
        commit_received := Head(sent_queue).m;
        sent_queue := Tail(sent_queue);
        print <<"RECEIVED COMMIT">>;
        replicaTermination_commit[self] := TRUE;
    RespondToClient:
        if (replicaTermination_commit[self]) then
            globalSeqNum := globalSeqNum + 1;
            msg_struct := [m |-> commit_received, sender |-> self, to |-> "client", seq |-> globalSeqNum, type |-> "client_response"]; \* Likely need to broadcast clients name to all replicas so that they all know who to send back to
            sent_queue := Append(sent_queue, msg_struct);
            print <<"Commit: message -> " \o msg_struct.m \o ", sender -> "  \o msg_struct.sender \o ", to -> "  \o msg_struct.to \o ", sequence# -> " \o ToString(msg_struct.seq)>>;
        end if;
    Terminate:
        replicaTermination[self] := TRUE;
end process;

process Client = "client"
variables
clientID = "client";
leader \in chosenLeader;
sending \in messageSet;
counter = 0;
threshold = 2;
begin
    Send: \*Send one message to arb leader
        globalSeqNum := globalSeqNum + 1;
           
        msg_struct := [m |-> sending, sender |-> clientID, to |-> leader, seq |-> globalSeqNum, type |-> "client_request"];
        sent_queue := Append(sent_queue, msg_struct);
            
        print <<"Client message added to queue: message -> " \o msg_struct.m \o ", sender -> "  \o msg_struct.sender \o ", sequence# -> " \o ToString(msg_struct.seq)>>;
        print <<"Sent queue length: " \o ToString(Len(sent_queue))>>;
            
    Receive_all:
        while counter < threshold do
            await (sent_queue # <<>> /\ Head(sent_queue).to = clientID /\ Head(sent_queue).type = "client_response");
                counter := counter + 1;
        end while;
    ServerComplete:
        print <<"Server echoed all available messages (RECEIVED ALL COMMITS)">>;
        serverTerminated := TRUE;
end process;


end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "1ace604d" /\ chksum(tla) = "f0b7dd23")
\* Process variable toSend of process Replica at line 79 col 1 changed to toSend_
CONSTANT defaultInitValue
VARIABLES pc, clientRequest, lastSent, replicaTermination_preprep, 
          replicaTermination_prepare, replicaTermination_commit, 
          replicaTermination, serverTerminated, sent_queue, sender, sentTo, 
          messageSet, globalSeqNum, msg_struct, stack

(* define statement *)
MessageTypes == {"preprepare", "prepare", "commit", "client_request", "client_response"}
ReplicaOrClient == replicaSet \cup {"client"}
MessageSet == {"m1"}

TypeOK ==
    /\ sent_queue \in Seq([type: MessageTypes,
                           sender: ReplicaOrClient,
                           to: ReplicaOrClient,
                           m: MessageSet,
                           seq: 1..100])
    /\ globalSeqNum \in Nat
    /\ replicaTermination_preprep \in [replicaSet -> BOOLEAN]
    /\ replicaTermination_prepare \in [replicaSet -> BOOLEAN]

StateConstraint ==
/\ globalSeqNum <= 3
/\ Len(sent_queue) <= 5

TerminationCorrectness == <>(\A r \in replicaSet : replicaTermination[r])

VARIABLES from, msg, type, toSend, message, preprep_received, 
          prepare_received, commit_received, toSend_, replicaID, client, 
          clientID, leader, sending, counter, threshold

vars == << pc, clientRequest, lastSent, replicaTermination_preprep, 
           replicaTermination_prepare, replicaTermination_commit, 
           replicaTermination, serverTerminated, sent_queue, sender, sentTo, 
           messageSet, globalSeqNum, msg_struct, stack, from, msg, type, 
           toSend, message, preprep_received, prepare_received, 
           commit_received, toSend_, replicaID, client, clientID, leader, 
           sending, counter, threshold >>

ProcSet == (replicaSet) \cup {"client"}

Init == (* Global variables *)
        /\ clientRequest = ""
        /\ lastSent = ""
        /\ replicaTermination_preprep = [r \in replicaSet |-> FALSE]
        /\ replicaTermination_prepare = [r \in replicaSet |-> FALSE]
        /\ replicaTermination_commit = [r \in replicaSet |-> FALSE]
        /\ replicaTermination = [r \in replicaSet |-> FALSE]
        /\ serverTerminated = FALSE
        /\ sent_queue = <<>>
        /\ sender = ""
        /\ sentTo = ""
        /\ messageSet = {"m1"}
        /\ globalSeqNum = 0
        /\ msg_struct = [m |-> "", sender |-> "", to |-> "", seq |-> 0, type |-> ""]
        (* Procedure Broadcast *)
        /\ from = [ self \in ProcSet |-> defaultInitValue]
        /\ msg = [ self \in ProcSet |-> defaultInitValue]
        /\ type = [ self \in ProcSet |-> defaultInitValue]
        /\ toSend = [ self \in ProcSet |-> replicaSet \ {from[self]}]
        (* Process Replica *)
        /\ message = [self \in replicaSet |-> ""]
        /\ preprep_received = [self \in replicaSet |-> ""]
        /\ prepare_received = [self \in replicaSet |-> ""]
        /\ commit_received = [self \in replicaSet |-> ""]
        /\ toSend_ = [self \in replicaSet |-> {}]
        /\ replicaID = [self \in replicaSet |-> self]
        /\ client = [self \in replicaSet |-> ""]
        (* Process Client *)
        /\ clientID = "client"
        /\ leader \in chosenLeader
        /\ sending \in messageSet
        /\ counter = 0
        /\ threshold = 2
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in replicaSet -> "PrimarySends"
                                        [] self = "client" -> "Send"]

BroadcastLoop(self) == /\ pc[self] = "BroadcastLoop"
                       /\ IF toSend[self] # {}
                             THEN /\ \E r \in toSend[self]:
                                       /\ globalSeqNum' = globalSeqNum + 1
                                       /\ msg_struct' = [m |-> msg[self], sender |-> from[self], to |-> r, seq |-> globalSeqNum', type |-> type[self]]
                                       /\ sent_queue' = Append(sent_queue, msg_struct')
                                       /\ toSend' = [toSend EXCEPT ![self] = toSend[self] \ {r}]
                                       /\ PrintT(<<"Replica " \o self \o " sent " \o msg_struct'.m \o " to " \o r \o ". Seq# -> " \o ToString(globalSeqNum') \o " | Type = " \o type[self]>>)
                                  /\ pc' = [pc EXCEPT ![self] = "BroadcastLoop"]
                                  /\ UNCHANGED << stack, from, msg, type >>
                             ELSE /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                  /\ toSend' = [toSend EXCEPT ![self] = Head(stack[self]).toSend]
                                  /\ from' = [from EXCEPT ![self] = Head(stack[self]).from]
                                  /\ msg' = [msg EXCEPT ![self] = Head(stack[self]).msg]
                                  /\ type' = [type EXCEPT ![self] = Head(stack[self]).type]
                                  /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                  /\ UNCHANGED << sent_queue, globalSeqNum, 
                                                  msg_struct >>
                       /\ UNCHANGED << clientRequest, lastSent, 
                                       replicaTermination_preprep, 
                                       replicaTermination_prepare, 
                                       replicaTermination_commit, 
                                       replicaTermination, serverTerminated, 
                                       sender, sentTo, messageSet, message, 
                                       preprep_received, prepare_received, 
                                       commit_received, toSend_, replicaID, 
                                       client, clientID, leader, sending, 
                                       counter, threshold >>

Broadcast(self) == BroadcastLoop(self)

PrimarySends(self) == /\ pc[self] = "PrimarySends"
                      /\ IF (chosenLeader = {self})
                            THEN /\ (sent_queue # <<>> /\ Head(sent_queue).to = self)
                                 /\ message' = [message EXCEPT ![self] = Head(sent_queue).m]
                                 /\ client' = [client EXCEPT ![self] = Head(sent_queue).sender]
                                 /\ sent_queue' = Tail(sent_queue)
                                 /\ pc' = [pc EXCEPT ![self] = "DoBroadcast"]
                            ELSE /\ pc' = [pc EXCEPT ![self] = "WaitForPrePrepare"]
                                 /\ UNCHANGED << sent_queue, message, client >>
                      /\ UNCHANGED << clientRequest, lastSent, 
                                      replicaTermination_preprep, 
                                      replicaTermination_prepare, 
                                      replicaTermination_commit, 
                                      replicaTermination, serverTerminated, 
                                      sender, sentTo, messageSet, globalSeqNum, 
                                      msg_struct, stack, from, msg, type, 
                                      toSend, preprep_received, 
                                      prepare_received, commit_received, 
                                      toSend_, replicaID, clientID, leader, 
                                      sending, counter, threshold >>

DoBroadcast(self) == /\ pc[self] = "DoBroadcast"
                     /\ /\ from' = [from EXCEPT ![self] = self]
                        /\ msg' = [msg EXCEPT ![self] = message[self]]
                        /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Broadcast",
                                                                 pc        |->  "SetPrePrepareMessage",
                                                                 toSend    |->  toSend[self],
                                                                 from      |->  from[self],
                                                                 msg       |->  msg[self],
                                                                 type      |->  type[self] ] >>
                                                             \o stack[self]]
                        /\ type' = [type EXCEPT ![self] = "preprepare"]
                     /\ toSend' = [toSend EXCEPT ![self] = replicaSet \ {from'[self]}]
                     /\ pc' = [pc EXCEPT ![self] = "BroadcastLoop"]
                     /\ UNCHANGED << clientRequest, lastSent, 
                                     replicaTermination_preprep, 
                                     replicaTermination_prepare, 
                                     replicaTermination_commit, 
                                     replicaTermination, serverTerminated, 
                                     sent_queue, sender, sentTo, messageSet, 
                                     globalSeqNum, msg_struct, message, 
                                     preprep_received, prepare_received, 
                                     commit_received, toSend_, replicaID, 
                                     client, clientID, leader, sending, 
                                     counter, threshold >>

SetPrePrepareMessage(self) == /\ pc[self] = "SetPrePrepareMessage"
                              /\ preprep_received' = [preprep_received EXCEPT ![self] = message[self]]
                              /\ replicaTermination_preprep' = [replicaTermination_preprep EXCEPT ![self] = TRUE]
                              /\ pc' = [pc EXCEPT ![self] = "SendPrepare"]
                              /\ UNCHANGED << clientRequest, lastSent, 
                                              replicaTermination_prepare, 
                                              replicaTermination_commit, 
                                              replicaTermination, 
                                              serverTerminated, sent_queue, 
                                              sender, sentTo, messageSet, 
                                              globalSeqNum, msg_struct, stack, 
                                              from, msg, type, toSend, message, 
                                              prepare_received, 
                                              commit_received, toSend_, 
                                              replicaID, client, clientID, 
                                              leader, sending, counter, 
                                              threshold >>

WaitForPrePrepare(self) == /\ pc[self] = "WaitForPrePrepare"
                           /\ (sent_queue # <<>> /\ Head(sent_queue).to = self /\ Head(sent_queue).type = "preprepare")
                           /\ preprep_received' = [preprep_received EXCEPT ![self] = Head(sent_queue).m]
                           /\ sent_queue' = Tail(sent_queue)
                           /\ PrintT(<<"Sent Queue now: " \o ToString(Len(sent_queue'))>>)
                           /\ replicaTermination_preprep' = [replicaTermination_preprep EXCEPT ![self] = TRUE]
                           /\ pc' = [pc EXCEPT ![self] = "SendPrepare"]
                           /\ UNCHANGED << clientRequest, lastSent, 
                                           replicaTermination_prepare, 
                                           replicaTermination_commit, 
                                           replicaTermination, 
                                           serverTerminated, sender, sentTo, 
                                           messageSet, globalSeqNum, 
                                           msg_struct, stack, from, msg, type, 
                                           toSend, message, prepare_received, 
                                           commit_received, toSend_, replicaID, 
                                           client, clientID, leader, sending, 
                                           counter, threshold >>

SendPrepare(self) == /\ pc[self] = "SendPrepare"
                     /\ IF (replicaTermination_preprep[self])
                           THEN /\ pc' = [pc EXCEPT ![self] = "DoPrepareBroadcast"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "WaitForPrepare"]
                     /\ UNCHANGED << clientRequest, lastSent, 
                                     replicaTermination_preprep, 
                                     replicaTermination_prepare, 
                                     replicaTermination_commit, 
                                     replicaTermination, serverTerminated, 
                                     sent_queue, sender, sentTo, messageSet, 
                                     globalSeqNum, msg_struct, stack, from, 
                                     msg, type, toSend, message, 
                                     preprep_received, prepare_received, 
                                     commit_received, toSend_, replicaID, 
                                     client, clientID, leader, sending, 
                                     counter, threshold >>

DoPrepareBroadcast(self) == /\ pc[self] = "DoPrepareBroadcast"
                            /\ PrintT(<<"BROADCASTING PREPARE">>)
                            /\ /\ from' = [from EXCEPT ![self] = self]
                               /\ msg' = [msg EXCEPT ![self] = preprep_received[self]]
                               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Broadcast",
                                                                        pc        |->  "WaitForPrepare",
                                                                        toSend    |->  toSend[self],
                                                                        from      |->  from[self],
                                                                        msg       |->  msg[self],
                                                                        type      |->  type[self] ] >>
                                                                    \o stack[self]]
                               /\ type' = [type EXCEPT ![self] = "prepare"]
                            /\ toSend' = [toSend EXCEPT ![self] = replicaSet \ {from'[self]}]
                            /\ pc' = [pc EXCEPT ![self] = "BroadcastLoop"]
                            /\ UNCHANGED << clientRequest, lastSent, 
                                            replicaTermination_preprep, 
                                            replicaTermination_prepare, 
                                            replicaTermination_commit, 
                                            replicaTermination, 
                                            serverTerminated, sent_queue, 
                                            sender, sentTo, messageSet, 
                                            globalSeqNum, msg_struct, message, 
                                            preprep_received, prepare_received, 
                                            commit_received, toSend_, 
                                            replicaID, client, clientID, 
                                            leader, sending, counter, 
                                            threshold >>

WaitForPrepare(self) == /\ pc[self] = "WaitForPrepare"
                        /\ (sent_queue # <<>> /\ Head(sent_queue).to = self /\ Head(sent_queue).type = "prepare")
                        /\ prepare_received' = [prepare_received EXCEPT ![self] = Head(sent_queue).m]
                        /\ sent_queue' = Tail(sent_queue)
                        /\ PrintT(<<"GETTING READY TO CAST COMMIT">>)
                        /\ replicaTermination_prepare' = [replicaTermination_prepare EXCEPT ![self] = TRUE]
                        /\ pc' = [pc EXCEPT ![self] = "SendCommit"]
                        /\ UNCHANGED << clientRequest, lastSent, 
                                        replicaTermination_preprep, 
                                        replicaTermination_commit, 
                                        replicaTermination, serverTerminated, 
                                        sender, sentTo, messageSet, 
                                        globalSeqNum, msg_struct, stack, from, 
                                        msg, type, toSend, message, 
                                        preprep_received, commit_received, 
                                        toSend_, replicaID, client, clientID, 
                                        leader, sending, counter, threshold >>

SendCommit(self) == /\ pc[self] = "SendCommit"
                    /\ IF (replicaTermination_prepare[self])
                          THEN /\ pc' = [pc EXCEPT ![self] = "DoCommitBroadcast"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "WaitForCommit"]
                    /\ UNCHANGED << clientRequest, lastSent, 
                                    replicaTermination_preprep, 
                                    replicaTermination_prepare, 
                                    replicaTermination_commit, 
                                    replicaTermination, serverTerminated, 
                                    sent_queue, sender, sentTo, messageSet, 
                                    globalSeqNum, msg_struct, stack, from, msg, 
                                    type, toSend, message, preprep_received, 
                                    prepare_received, commit_received, toSend_, 
                                    replicaID, client, clientID, leader, 
                                    sending, counter, threshold >>

DoCommitBroadcast(self) == /\ pc[self] = "DoCommitBroadcast"
                           /\ PrintT(<<"BROADCASTING COMMIT">>)
                           /\ /\ from' = [from EXCEPT ![self] = self]
                              /\ msg' = [msg EXCEPT ![self] = prepare_received[self]]
                              /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Broadcast",
                                                                       pc        |->  "WaitForCommit",
                                                                       toSend    |->  toSend[self],
                                                                       from      |->  from[self],
                                                                       msg       |->  msg[self],
                                                                       type      |->  type[self] ] >>
                                                                   \o stack[self]]
                              /\ type' = [type EXCEPT ![self] = "commit"]
                           /\ toSend' = [toSend EXCEPT ![self] = replicaSet \ {from'[self]}]
                           /\ pc' = [pc EXCEPT ![self] = "BroadcastLoop"]
                           /\ UNCHANGED << clientRequest, lastSent, 
                                           replicaTermination_preprep, 
                                           replicaTermination_prepare, 
                                           replicaTermination_commit, 
                                           replicaTermination, 
                                           serverTerminated, sent_queue, 
                                           sender, sentTo, messageSet, 
                                           globalSeqNum, msg_struct, message, 
                                           preprep_received, prepare_received, 
                                           commit_received, toSend_, replicaID, 
                                           client, clientID, leader, sending, 
                                           counter, threshold >>

WaitForCommit(self) == /\ pc[self] = "WaitForCommit"
                       /\ (sent_queue # <<>> /\ Head(sent_queue).to = self /\ Head(sent_queue).type = "commit")
                       /\ commit_received' = [commit_received EXCEPT ![self] = Head(sent_queue).m]
                       /\ sent_queue' = Tail(sent_queue)
                       /\ PrintT(<<"RECEIVED COMMIT">>)
                       /\ replicaTermination_commit' = [replicaTermination_commit EXCEPT ![self] = TRUE]
                       /\ pc' = [pc EXCEPT ![self] = "RespondToClient"]
                       /\ UNCHANGED << clientRequest, lastSent, 
                                       replicaTermination_preprep, 
                                       replicaTermination_prepare, 
                                       replicaTermination, serverTerminated, 
                                       sender, sentTo, messageSet, 
                                       globalSeqNum, msg_struct, stack, from, 
                                       msg, type, toSend, message, 
                                       preprep_received, prepare_received, 
                                       toSend_, replicaID, client, clientID, 
                                       leader, sending, counter, threshold >>

RespondToClient(self) == /\ pc[self] = "RespondToClient"
                         /\ IF (replicaTermination_commit[self])
                               THEN /\ globalSeqNum' = globalSeqNum + 1
                                    /\ msg_struct' = [m |-> commit_received[self], sender |-> self, to |-> "client", seq |-> globalSeqNum', type |-> "client_response"]
                                    /\ sent_queue' = Append(sent_queue, msg_struct')
                                    /\ PrintT(<<"Commit: message -> " \o msg_struct'.m \o ", sender -> "  \o msg_struct'.sender \o ", to -> "  \o msg_struct'.to \o ", sequence# -> " \o ToString(msg_struct'.seq)>>)
                               ELSE /\ TRUE
                                    /\ UNCHANGED << sent_queue, globalSeqNum, 
                                                    msg_struct >>
                         /\ pc' = [pc EXCEPT ![self] = "Terminate"]
                         /\ UNCHANGED << clientRequest, lastSent, 
                                         replicaTermination_preprep, 
                                         replicaTermination_prepare, 
                                         replicaTermination_commit, 
                                         replicaTermination, serverTerminated, 
                                         sender, sentTo, messageSet, stack, 
                                         from, msg, type, toSend, message, 
                                         preprep_received, prepare_received, 
                                         commit_received, toSend_, replicaID, 
                                         client, clientID, leader, sending, 
                                         counter, threshold >>

Terminate(self) == /\ pc[self] = "Terminate"
                   /\ replicaTermination' = [replicaTermination EXCEPT ![self] = TRUE]
                   /\ pc' = [pc EXCEPT ![self] = "Done"]
                   /\ UNCHANGED << clientRequest, lastSent, 
                                   replicaTermination_preprep, 
                                   replicaTermination_prepare, 
                                   replicaTermination_commit, serverTerminated, 
                                   sent_queue, sender, sentTo, messageSet, 
                                   globalSeqNum, msg_struct, stack, from, msg, 
                                   type, toSend, message, preprep_received, 
                                   prepare_received, commit_received, toSend_, 
                                   replicaID, client, clientID, leader, 
                                   sending, counter, threshold >>

Replica(self) == PrimarySends(self) \/ DoBroadcast(self)
                    \/ SetPrePrepareMessage(self)
                    \/ WaitForPrePrepare(self) \/ SendPrepare(self)
                    \/ DoPrepareBroadcast(self) \/ WaitForPrepare(self)
                    \/ SendCommit(self) \/ DoCommitBroadcast(self)
                    \/ WaitForCommit(self) \/ RespondToClient(self)
                    \/ Terminate(self)

Send == /\ pc["client"] = "Send"
        /\ globalSeqNum' = globalSeqNum + 1
        /\ msg_struct' = [m |-> sending, sender |-> clientID, to |-> leader, seq |-> globalSeqNum', type |-> "client_request"]
        /\ sent_queue' = Append(sent_queue, msg_struct')
        /\ PrintT(<<"Client message added to queue: message -> " \o msg_struct'.m \o ", sender -> "  \o msg_struct'.sender \o ", sequence# -> " \o ToString(msg_struct'.seq)>>)
        /\ PrintT(<<"Sent queue length: " \o ToString(Len(sent_queue'))>>)
        /\ pc' = [pc EXCEPT !["client"] = "Receive_all"]
        /\ UNCHANGED << clientRequest, lastSent, replicaTermination_preprep, 
                        replicaTermination_prepare, replicaTermination_commit, 
                        replicaTermination, serverTerminated, sender, sentTo, 
                        messageSet, stack, from, msg, type, toSend, message, 
                        preprep_received, prepare_received, commit_received, 
                        toSend_, replicaID, client, clientID, leader, sending, 
                        counter, threshold >>

Receive_all == /\ pc["client"] = "Receive_all"
               /\ IF counter < threshold
                     THEN /\ (sent_queue # <<>> /\ Head(sent_queue).to = clientID /\ Head(sent_queue).type = "client_response")
                          /\ counter' = counter + 1
                          /\ pc' = [pc EXCEPT !["client"] = "Receive_all"]
                     ELSE /\ pc' = [pc EXCEPT !["client"] = "ServerComplete"]
                          /\ UNCHANGED counter
               /\ UNCHANGED << clientRequest, lastSent, 
                               replicaTermination_preprep, 
                               replicaTermination_prepare, 
                               replicaTermination_commit, replicaTermination, 
                               serverTerminated, sent_queue, sender, sentTo, 
                               messageSet, globalSeqNum, msg_struct, stack, 
                               from, msg, type, toSend, message, 
                               preprep_received, prepare_received, 
                               commit_received, toSend_, replicaID, client, 
                               clientID, leader, sending, threshold >>

ServerComplete == /\ pc["client"] = "ServerComplete"
                  /\ PrintT(<<"Server echoed all available messages (RECEIVED ALL COMMITS)">>)
                  /\ serverTerminated' = TRUE
                  /\ pc' = [pc EXCEPT !["client"] = "Done"]
                  /\ UNCHANGED << clientRequest, lastSent, 
                                  replicaTermination_preprep, 
                                  replicaTermination_prepare, 
                                  replicaTermination_commit, 
                                  replicaTermination, sent_queue, sender, 
                                  sentTo, messageSet, globalSeqNum, msg_struct, 
                                  stack, from, msg, type, toSend, message, 
                                  preprep_received, prepare_received, 
                                  commit_received, toSend_, replicaID, client, 
                                  clientID, leader, sending, counter, 
                                  threshold >>

Client == Send \/ Receive_all \/ ServerComplete

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Client
           \/ (\E self \in ProcSet: Broadcast(self))
           \/ (\E self \in replicaSet: Replica(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Wed Nov 12 01:39:30 PST 2025 by daineyip
\* Created Mon Nov 10 00:59:31 PST 2025 by daineyip
