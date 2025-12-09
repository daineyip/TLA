---------------------- MODULE PBFT_messagelogrefactor ----------------------
EXTENDS Integers, Sequences, TLC, FiniteSets
CONSTANT replicaSet, chosenLeader

(* --algorithm echo

variables
replicaTermination = [r \in replicaSet |-> FALSE];
serverTerminated = FALSE;
\*chosenLeader = "c1"; \* Implement leader lock later
inbox = [r \in replicaSet \cup {"client"} |-> <<>>]; \*Client should be dynamically set
sender = "";
messageSet = {"m1"};
globalSeqNum = 0;
state = [r \in replicaSet \cup {"client"} |-> "init"];
received_log = [r \in replicaSet \cup {"client"} |-> {}];
msg_struct = [m |-> "", sender |-> "", to |-> "", seq |-> 0, type |-> ""];

define
    ReplicaStates == {"init", "prepared", "committed", "done"}

    MessageTypes == {"preprepare", "prepare", "commit", "client_request", "client_response"}
    ReplicaOrClient == replicaSet \cup {"client"}
    MessageSet == {"m1"}
    
    MessageRecords == [type: MessageTypes,
                       sender: ReplicaOrClient,
                       m: MessageSet,
                       seq: Nat,
                       to: ReplicaOrClient]

    TypeOK ==
        /\ globalSeqNum \in Nat
        /\ inbox \in [ReplicaOrClient -> Seq(MessageRecords)]
        /\ replicaTermination \in [replicaSet -> BOOLEAN]
        /\ state \in [replicaSet \cup {"client"} -> ReplicaStates]
        /\ received_log \in [replicaSet \cup {"client"} -> SUBSET MessageRecords]

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
                inbox[r] := Append(inbox[r], msg_struct);
                toSend := toSend \ {r};
                print <<"Replica " \o self \o " sent " \o msg_struct.m \o " to " \o r \o ". Seq# -> " \o ToString(globalSeqNum) \o " | Type = " \o type>>;
            end with;
        end while;
    return;
end procedure;

fair process Replica \in replicaSet
variables
message = "";
toSend = {};
client = "";
begin
    PrimarySends:
        if (chosenLeader = {self}) then
            await (inbox[self] # <<>>);
            msg_struct := Head(inbox[self]);
            client := Head(inbox[self]).sender;
            inbox[self] := Tail(inbox[self]);
            
            DoBroadcast:
                call Broadcast(self, msg_struct.m, "preprepare");
            
            AddToLog:                
                globalSeqNum := globalSeqNum + 1;
                received_log[self] := received_log[self] \cup {[m |-> msg_struct.m, sender |-> self, to |-> self, seq |-> globalSeqNum, type |-> "preprepare"]};
        end if;
    
    MessageHandling:
        while state[self] # "done" do
            await inbox[self] # <<>>;
            msg_struct := Head(inbox[self]);
            inbox[self] := Tail(inbox[self]);
            
            received_log[self] := received_log[self] \cup {msg_struct};
            
            Prepare:
                if state[self] = "init" /\ (\E m \in received_log[self] : m.type = "preprepare") then
                    PrePrepareBroadcast:
                        with m \in {x \in received_log[self] : x.type = "preprepare"} do
                            call Broadcast(self, m.m, "prepare");
                        end with;
                    SetStatePrepared:
                        state[self] := "prepared";
                end if;
            
            Commit:
                if state[self] = "prepared" /\
                    (Cardinality({m \in received_log[self] : m.type = "prepare"}) >= Cardinality(replicaSet)-1) then
                        PrepareBroadcast:
                            with m \in {x \in received_log[self] : x.type = "prepare"} do
                                call Broadcast(self, m.m, "commit");
                            end with;
                        SetStateCommitted:
                            state[self] := "committed";
                end if ;
            
            RespondToClient:
                if state[self] = "committed" /\ 
                   (\E v \in MessageSet : 
                        Cardinality({m \in received_log[self] : m.type = "commit" /\ m.m = v}) >= Cardinality(replicaSet) - 1) 
                then
                    with winning_val = CHOOSE v \in MessageSet : 
                                       Cardinality({m \in received_log[self] : m.type = "commit" /\ m.m = v}) >= Cardinality(replicaSet) - 1 
                    do
                        globalSeqNum := globalSeqNum + 1;
                        
                        msg_struct := [m |-> winning_val, 
                                       sender |-> self, 
                                       to |-> "client", 
                                       seq |-> globalSeqNum, 
                                       type |-> "client_response"];
                                       
                        inbox["client"] := Append(inbox["client"], msg_struct);
                        
                        state[self] := "done";
                        replicaTermination[self] := TRUE;
                    end with;
                end if;
        end while; 
        
    Terminate:
        replicaTermination[self] := TRUE;  
end process;                    

fair process Client = "client"
variables
clientID = "client";
leader \in chosenLeader;
sending \in messageSet;
threshold = Cardinality(replicaSet); \*2f+1 logic needed here
begin
    Send:
        globalSeqNum := globalSeqNum + 1;
           
        msg_struct := [m |-> sending, sender |-> clientID, to |-> leader, seq |-> globalSeqNum, type |-> "client_request"];
        inbox[leader] := Append(inbox[leader], msg_struct);
            
        print <<"Client message added to queue: message -> " \o msg_struct.m \o ", sender -> "  \o msg_struct.sender \o ", sequence# -> " \o ToString(msg_struct.seq)>>;
        print <<"Sent queue length: " \o ToString(Len(inbox[clientID]))>>;
            
    Receive_all:
        while state[clientID] # "done" do
            await inbox[clientID] # <<>>;
                msg_struct := Head(inbox[clientID]);
                inbox[clientID] := Tail(inbox[clientID]);
            
                received_log[clientID] := received_log[clientID] \cup {msg_struct};
            
            CompleteServer:
                if (Cardinality({m \in received_log[clientID] : m.type = "client_response"}) >= Cardinality(replicaSet)) then
                    print <<"Server echoed all available messages (RECEIVED ALL COMMITS)">>;
                    state[clientID] := "done";
                    serverTerminated := TRUE;
                end if ; 
        end while;
end process;


end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "90f4a6f" /\ chksum(tla) = "6f258b67")
\* Process variable toSend of process Replica at line 63 col 1 changed to toSend_
CONSTANT defaultInitValue
VARIABLES pc, replicaTermination, serverTerminated, inbox, sender, messageSet, 
          globalSeqNum, state, received_log, msg_struct, stack

(* define statement *)
ReplicaStates == {"init", "prepared", "committed", "done"}

MessageTypes == {"preprepare", "prepare", "commit", "client_request", "client_response"}
ReplicaOrClient == replicaSet \cup {"client"}
MessageSet == {"m1"}

MessageRecords == [type: MessageTypes,
                   sender: ReplicaOrClient,
                   m: MessageSet,
                   seq: Nat,
                   to: ReplicaOrClient]

TypeOK ==
    /\ globalSeqNum \in Nat
    /\ inbox \in [ReplicaOrClient -> Seq(MessageRecords)]
    /\ replicaTermination \in [replicaSet -> BOOLEAN]
    /\ state \in [replicaSet \cup {"client"} -> ReplicaStates]
    /\ received_log \in [replicaSet \cup {"client"} -> SUBSET MessageRecords]

TerminationCorrectness == <>(\A r \in replicaSet : replicaTermination[r])

VARIABLES from, msg, type, toSend, message, toSend_, client, clientID, leader, 
          sending, threshold

vars == << pc, replicaTermination, serverTerminated, inbox, sender, 
           messageSet, globalSeqNum, state, received_log, msg_struct, stack, 
           from, msg, type, toSend, message, toSend_, client, clientID, 
           leader, sending, threshold >>

ProcSet == (replicaSet) \cup {"client"}

Init == (* Global variables *)
        /\ replicaTermination = [r \in replicaSet |-> FALSE]
        /\ serverTerminated = FALSE
        /\ inbox = [r \in replicaSet \cup {"client"} |-> <<>>]
        /\ sender = ""
        /\ messageSet = {"m1"}
        /\ globalSeqNum = 0
        /\ state = [r \in replicaSet \cup {"client"} |-> "init"]
        /\ received_log = [r \in replicaSet \cup {"client"} |-> {}]
        /\ msg_struct = [m |-> "", sender |-> "", to |-> "", seq |-> 0, type |-> ""]
        (* Procedure Broadcast *)
        /\ from = [ self \in ProcSet |-> defaultInitValue]
        /\ msg = [ self \in ProcSet |-> defaultInitValue]
        /\ type = [ self \in ProcSet |-> defaultInitValue]
        /\ toSend = [ self \in ProcSet |-> replicaSet \ {from[self]}]
        (* Process Replica *)
        /\ message = [self \in replicaSet |-> ""]
        /\ toSend_ = [self \in replicaSet |-> {}]
        /\ client = [self \in replicaSet |-> ""]
        (* Process Client *)
        /\ clientID = "client"
        /\ leader \in chosenLeader
        /\ sending \in messageSet
        /\ threshold = Cardinality(replicaSet)
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in replicaSet -> "PrimarySends"
                                        [] self = "client" -> "Send"]

BroadcastLoop(self) == /\ pc[self] = "BroadcastLoop"
                       /\ IF toSend[self] # {}
                             THEN /\ \E r \in toSend[self]:
                                       /\ globalSeqNum' = globalSeqNum + 1
                                       /\ msg_struct' = [m |-> msg[self], sender |-> from[self], to |-> r, seq |-> globalSeqNum', type |-> type[self]]
                                       /\ inbox' = [inbox EXCEPT ![r] = Append(inbox[r], msg_struct')]
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
                                  /\ UNCHANGED << inbox, globalSeqNum, 
                                                  msg_struct >>
                       /\ UNCHANGED << replicaTermination, serverTerminated, 
                                       sender, messageSet, state, received_log, 
                                       message, toSend_, client, clientID, 
                                       leader, sending, threshold >>

Broadcast(self) == BroadcastLoop(self)

PrimarySends(self) == /\ pc[self] = "PrimarySends"
                      /\ IF (chosenLeader = {self})
                            THEN /\ (inbox[self] # <<>>)
                                 /\ msg_struct' = Head(inbox[self])
                                 /\ client' = [client EXCEPT ![self] = Head(inbox[self]).sender]
                                 /\ inbox' = [inbox EXCEPT ![self] = Tail(inbox[self])]
                                 /\ pc' = [pc EXCEPT ![self] = "DoBroadcast"]
                            ELSE /\ pc' = [pc EXCEPT ![self] = "MessageHandling"]
                                 /\ UNCHANGED << inbox, msg_struct, client >>
                      /\ UNCHANGED << replicaTermination, serverTerminated, 
                                      sender, messageSet, globalSeqNum, state, 
                                      received_log, stack, from, msg, type, 
                                      toSend, message, toSend_, clientID, 
                                      leader, sending, threshold >>

DoBroadcast(self) == /\ pc[self] = "DoBroadcast"
                     /\ /\ from' = [from EXCEPT ![self] = self]
                        /\ msg' = [msg EXCEPT ![self] = msg_struct.m]
                        /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Broadcast",
                                                                 pc        |->  "AddToLog",
                                                                 toSend    |->  toSend[self],
                                                                 from      |->  from[self],
                                                                 msg       |->  msg[self],
                                                                 type      |->  type[self] ] >>
                                                             \o stack[self]]
                        /\ type' = [type EXCEPT ![self] = "preprepare"]
                     /\ toSend' = [toSend EXCEPT ![self] = replicaSet \ {from'[self]}]
                     /\ pc' = [pc EXCEPT ![self] = "BroadcastLoop"]
                     /\ UNCHANGED << replicaTermination, serverTerminated, 
                                     inbox, sender, messageSet, globalSeqNum, 
                                     state, received_log, msg_struct, message, 
                                     toSend_, client, clientID, leader, 
                                     sending, threshold >>

AddToLog(self) == /\ pc[self] = "AddToLog"
                  /\ globalSeqNum' = globalSeqNum + 1
                  /\ received_log' = [received_log EXCEPT ![self] = received_log[self] \cup {[m |-> msg_struct.m, sender |-> self, to |-> self, seq |-> globalSeqNum', type |-> "preprepare"]}]
                  /\ pc' = [pc EXCEPT ![self] = "MessageHandling"]
                  /\ UNCHANGED << replicaTermination, serverTerminated, inbox, 
                                  sender, messageSet, state, msg_struct, stack, 
                                  from, msg, type, toSend, message, toSend_, 
                                  client, clientID, leader, sending, threshold >>

MessageHandling(self) == /\ pc[self] = "MessageHandling"
                         /\ IF state[self] # "done"
                               THEN /\ inbox[self] # <<>>
                                    /\ msg_struct' = Head(inbox[self])
                                    /\ inbox' = [inbox EXCEPT ![self] = Tail(inbox[self])]
                                    /\ received_log' = [received_log EXCEPT ![self] = received_log[self] \cup {msg_struct'}]
                                    /\ pc' = [pc EXCEPT ![self] = "Prepare"]
                               ELSE /\ pc' = [pc EXCEPT ![self] = "Terminate"]
                                    /\ UNCHANGED << inbox, received_log, 
                                                    msg_struct >>
                         /\ UNCHANGED << replicaTermination, serverTerminated, 
                                         sender, messageSet, globalSeqNum, 
                                         state, stack, from, msg, type, toSend, 
                                         message, toSend_, client, clientID, 
                                         leader, sending, threshold >>

Prepare(self) == /\ pc[self] = "Prepare"
                 /\ IF state[self] = "init" /\ (\E m \in received_log[self] : m.type = "preprepare")
                       THEN /\ pc' = [pc EXCEPT ![self] = "PrePrepareBroadcast"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "Commit"]
                 /\ UNCHANGED << replicaTermination, serverTerminated, inbox, 
                                 sender, messageSet, globalSeqNum, state, 
                                 received_log, msg_struct, stack, from, msg, 
                                 type, toSend, message, toSend_, client, 
                                 clientID, leader, sending, threshold >>

PrePrepareBroadcast(self) == /\ pc[self] = "PrePrepareBroadcast"
                             /\ \E m \in {x \in received_log[self] : x.type = "preprepare"}:
                                  /\ /\ from' = [from EXCEPT ![self] = self]
                                     /\ msg' = [msg EXCEPT ![self] = m.m]
                                     /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Broadcast",
                                                                              pc        |->  "SetStatePrepared",
                                                                              toSend    |->  toSend[self],
                                                                              from      |->  from[self],
                                                                              msg       |->  msg[self],
                                                                              type      |->  type[self] ] >>
                                                                          \o stack[self]]
                                     /\ type' = [type EXCEPT ![self] = "prepare"]
                                  /\ toSend' = [toSend EXCEPT ![self] = replicaSet \ {from'[self]}]
                                  /\ pc' = [pc EXCEPT ![self] = "BroadcastLoop"]
                             /\ UNCHANGED << replicaTermination, 
                                             serverTerminated, inbox, sender, 
                                             messageSet, globalSeqNum, state, 
                                             received_log, msg_struct, message, 
                                             toSend_, client, clientID, leader, 
                                             sending, threshold >>

SetStatePrepared(self) == /\ pc[self] = "SetStatePrepared"
                          /\ state' = [state EXCEPT ![self] = "prepared"]
                          /\ pc' = [pc EXCEPT ![self] = "Commit"]
                          /\ UNCHANGED << replicaTermination, serverTerminated, 
                                          inbox, sender, messageSet, 
                                          globalSeqNum, received_log, 
                                          msg_struct, stack, from, msg, type, 
                                          toSend, message, toSend_, client, 
                                          clientID, leader, sending, threshold >>

Commit(self) == /\ pc[self] = "Commit"
                /\ IF state[self] = "prepared" /\
                       (Cardinality({m \in received_log[self] : m.type = "prepare"}) >= Cardinality(replicaSet)-1)
                      THEN /\ pc' = [pc EXCEPT ![self] = "PrepareBroadcast"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "RespondToClient"]
                /\ UNCHANGED << replicaTermination, serverTerminated, inbox, 
                                sender, messageSet, globalSeqNum, state, 
                                received_log, msg_struct, stack, from, msg, 
                                type, toSend, message, toSend_, client, 
                                clientID, leader, sending, threshold >>

PrepareBroadcast(self) == /\ pc[self] = "PrepareBroadcast"
                          /\ \E m \in {x \in received_log[self] : x.type = "prepare"}:
                               /\ /\ from' = [from EXCEPT ![self] = self]
                                  /\ msg' = [msg EXCEPT ![self] = m.m]
                                  /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Broadcast",
                                                                           pc        |->  "SetStateCommitted",
                                                                           toSend    |->  toSend[self],
                                                                           from      |->  from[self],
                                                                           msg       |->  msg[self],
                                                                           type      |->  type[self] ] >>
                                                                       \o stack[self]]
                                  /\ type' = [type EXCEPT ![self] = "commit"]
                               /\ toSend' = [toSend EXCEPT ![self] = replicaSet \ {from'[self]}]
                               /\ pc' = [pc EXCEPT ![self] = "BroadcastLoop"]
                          /\ UNCHANGED << replicaTermination, serverTerminated, 
                                          inbox, sender, messageSet, 
                                          globalSeqNum, state, received_log, 
                                          msg_struct, message, toSend_, client, 
                                          clientID, leader, sending, threshold >>

SetStateCommitted(self) == /\ pc[self] = "SetStateCommitted"
                           /\ state' = [state EXCEPT ![self] = "committed"]
                           /\ pc' = [pc EXCEPT ![self] = "RespondToClient"]
                           /\ UNCHANGED << replicaTermination, 
                                           serverTerminated, inbox, sender, 
                                           messageSet, globalSeqNum, 
                                           received_log, msg_struct, stack, 
                                           from, msg, type, toSend, message, 
                                           toSend_, client, clientID, leader, 
                                           sending, threshold >>

RespondToClient(self) == /\ pc[self] = "RespondToClient"
                         /\ IF state[self] = "committed" /\
                               (\E v \in MessageSet :
                                    Cardinality({m \in received_log[self] : m.type = "commit" /\ m.m = v}) >= Cardinality(replicaSet) - 1)
                               THEN /\ LET winning_val == CHOOSE v \in MessageSet :
                                                          Cardinality({m \in received_log[self] : m.type = "commit" /\ m.m = v}) >= Cardinality(replicaSet) - 1 IN
                                         /\ globalSeqNum' = globalSeqNum + 1
                                         /\ msg_struct' = [m |-> winning_val,
                                                           sender |-> self,
                                                           to |-> "client",
                                                           seq |-> globalSeqNum',
                                                           type |-> "client_response"]
                                         /\ inbox' = [inbox EXCEPT !["client"] = Append(inbox["client"], msg_struct')]
                                         /\ state' = [state EXCEPT ![self] = "done"]
                                         /\ replicaTermination' = [replicaTermination EXCEPT ![self] = TRUE]
                               ELSE /\ TRUE
                                    /\ UNCHANGED << replicaTermination, inbox, 
                                                    globalSeqNum, state, 
                                                    msg_struct >>
                         /\ pc' = [pc EXCEPT ![self] = "MessageHandling"]
                         /\ UNCHANGED << serverTerminated, sender, messageSet, 
                                         received_log, stack, from, msg, type, 
                                         toSend, message, toSend_, client, 
                                         clientID, leader, sending, threshold >>

Terminate(self) == /\ pc[self] = "Terminate"
                   /\ replicaTermination' = [replicaTermination EXCEPT ![self] = TRUE]
                   /\ pc' = [pc EXCEPT ![self] = "Done"]
                   /\ UNCHANGED << serverTerminated, inbox, sender, messageSet, 
                                   globalSeqNum, state, received_log, 
                                   msg_struct, stack, from, msg, type, toSend, 
                                   message, toSend_, client, clientID, leader, 
                                   sending, threshold >>

Replica(self) == PrimarySends(self) \/ DoBroadcast(self) \/ AddToLog(self)
                    \/ MessageHandling(self) \/ Prepare(self)
                    \/ PrePrepareBroadcast(self) \/ SetStatePrepared(self)
                    \/ Commit(self) \/ PrepareBroadcast(self)
                    \/ SetStateCommitted(self) \/ RespondToClient(self)
                    \/ Terminate(self)

Send == /\ pc["client"] = "Send"
        /\ globalSeqNum' = globalSeqNum + 1
        /\ msg_struct' = [m |-> sending, sender |-> clientID, to |-> leader, seq |-> globalSeqNum', type |-> "client_request"]
        /\ inbox' = [inbox EXCEPT ![leader] = Append(inbox[leader], msg_struct')]
        /\ PrintT(<<"Client message added to queue: message -> " \o msg_struct'.m \o ", sender -> "  \o msg_struct'.sender \o ", sequence# -> " \o ToString(msg_struct'.seq)>>)
        /\ PrintT(<<"Sent queue length: " \o ToString(Len(inbox'[clientID]))>>)
        /\ pc' = [pc EXCEPT !["client"] = "Receive_all"]
        /\ UNCHANGED << replicaTermination, serverTerminated, sender, 
                        messageSet, state, received_log, stack, from, msg, 
                        type, toSend, message, toSend_, client, clientID, 
                        leader, sending, threshold >>

Receive_all == /\ pc["client"] = "Receive_all"
               /\ IF state[clientID] # "done"
                     THEN /\ inbox[clientID] # <<>>
                          /\ msg_struct' = Head(inbox[clientID])
                          /\ inbox' = [inbox EXCEPT ![clientID] = Tail(inbox[clientID])]
                          /\ received_log' = [received_log EXCEPT ![clientID] = received_log[clientID] \cup {msg_struct'}]
                          /\ pc' = [pc EXCEPT !["client"] = "CompleteServer"]
                     ELSE /\ pc' = [pc EXCEPT !["client"] = "Done"]
                          /\ UNCHANGED << inbox, received_log, msg_struct >>
               /\ UNCHANGED << replicaTermination, serverTerminated, sender, 
                               messageSet, globalSeqNum, state, stack, from, 
                               msg, type, toSend, message, toSend_, client, 
                               clientID, leader, sending, threshold >>

CompleteServer == /\ pc["client"] = "CompleteServer"
                  /\ IF (Cardinality({m \in received_log[clientID] : m.type = "client_response"}) >= Cardinality(replicaSet))
                        THEN /\ PrintT(<<"Server echoed all available messages (RECEIVED ALL COMMITS)">>)
                             /\ state' = [state EXCEPT ![clientID] = "done"]
                             /\ serverTerminated' = TRUE
                        ELSE /\ TRUE
                             /\ UNCHANGED << serverTerminated, state >>
                  /\ pc' = [pc EXCEPT !["client"] = "Receive_all"]
                  /\ UNCHANGED << replicaTermination, inbox, sender, 
                                  messageSet, globalSeqNum, received_log, 
                                  msg_struct, stack, from, msg, type, toSend, 
                                  message, toSend_, client, clientID, leader, 
                                  sending, threshold >>

Client == Send \/ Receive_all \/ CompleteServer

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Client
           \/ (\E self \in ProcSet: Broadcast(self))
           \/ (\E self \in replicaSet: Replica(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in replicaSet : WF_vars(Replica(self)) /\ WF_vars(Broadcast(self))
        /\ WF_vars(Client)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Mon Dec 08 23:42:28 PST 2025 by daineyip
\* Created Sat Dec 06 16:32:56 PST 2025 by daineyip
