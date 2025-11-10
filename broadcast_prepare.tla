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
replicaTerminated = [r \in replicaSet |-> FALSE];
serverTerminated = FALSE;
\*chosenLeader = "c1"; \* Implement leader lock later
sent_queue = <<>>;
sender = "";
sentTo = "";
messageSet = {"m1"};
globalSeqNum = 0;
msg_struct = [m |-> "", sender |-> "", to |-> "", seq |-> 0];


define
\*    CorrectnessInvariant ==
\*        /\ (serverResponse # "" /\ lastSent # "") =>
\*           (serverResponse = lastSent) \* This will fail with 2 rounds
    SystemTermination == replicaTerminated
\*    TerminationCorrectness == SystemTermination => FALSE
       TerminationCorrectness == <>(\A r \in replicaSet : replicaTerminated[r])
       LeaderInSet == chosenLeader \in replicaSet
    EventuallyClientSends == <>(Len(sent_queue) > 0)

\*      TerminationCorrectness == clientTerminated

end define;

process Replica \in replicaSet
variables
\*sending \in messageSet;
message = "";
toSend = {};
replicaID = self;
\* local memory for last sent
begin
    Broadcast:
        if (chosenLeader = {self}) then
            await (sent_queue # <<>> /\ Head(sent_queue).to = self);
            message := Head(sent_queue).m;
            sent_queue := Tail(sent_queue);
            toSend := replicaSet \ {self};
            BroadcastLoop:
                while toSend # {} do
                    with r \in toSend do
                        globalSeqNum := globalSeqNum + 1;
                        msg_struct := [m |-> message, sender |-> self, to |-> r, seq |-> globalSeqNum];
                        sent_queue := Append(sent_queue, msg_struct);
                        toSend := toSend \ {r};
                        print <<"Replica " \o self \o " sent " \o msg_struct.m \o " to " \o r \o ". Seq# -> " \o ToString(globalSeqNum)>>;
                    end with;
                end while;
            replicaTerminated[self] := TRUE;
        end if;
    WaitForEcho:
        await (sent_queue # <<>> /\ Head(sent_queue).to = self);
        sent_queue := Tail(sent_queue);
        print <<"Sent Queue now: " \o ToString(Len(sent_queue))>>;
    replicaTerminated[self] := TRUE;
end process;

process Client = "client"
variables
clientID = "client";
leader \in chosenLeader;
sending \in messageSet;
begin
    Send: \*Send one message to arb leader
        globalSeqNum := globalSeqNum + 1;
           
        msg_struct := [m |-> sending, sender |-> clientID, to |-> leader, seq |-> globalSeqNum];
        sent_queue := Append(sent_queue, msg_struct);
            
        print <<"Client message added to queue: message -> " \o msg_struct.m \o ", sender -> "  \o msg_struct.sender \o ", sequence# -> " \o ToString(msg_struct.seq)>>;
        print <<"Sent queue length: " \o ToString(Len(sent_queue))>>;
            
    Receive_all:
        print <<"Receiving">>;
\*    Receive Loop
    ServerComplete:
        print <<"Server echoed all available messages">>;
        serverTerminated := TRUE;
end process;


end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "ad813cfb" /\ chksum(tla) = "ac20eb82")
VARIABLES pc, clientRequest, lastSent, replicaTerminated, serverTerminated, 
          sent_queue, sender, sentTo, messageSet, globalSeqNum, msg_struct

(* define statement *)
SystemTermination == replicaTerminated

   TerminationCorrectness == <>(\A r \in replicaSet : replicaTerminated[r])
   LeaderInSet == chosenLeader \in replicaSet
EventuallyClientSends == <>(Len(sent_queue) > 0)

VARIABLES message, toSend, replicaID, clientID, leader, sending

vars == << pc, clientRequest, lastSent, replicaTerminated, serverTerminated, 
           sent_queue, sender, sentTo, messageSet, globalSeqNum, msg_struct, 
           message, toSend, replicaID, clientID, leader, sending >>

ProcSet == (replicaSet) \cup {"client"}

Init == (* Global variables *)
        /\ clientRequest = ""
        /\ lastSent = ""
        /\ replicaTerminated = [r \in replicaSet |-> FALSE]
        /\ serverTerminated = FALSE
        /\ sent_queue = <<>>
        /\ sender = ""
        /\ sentTo = ""
        /\ messageSet = {"m1"}
        /\ globalSeqNum = 0
        /\ msg_struct = [m |-> "", sender |-> "", to |-> "", seq |-> 0]
        (* Process Replica *)
        /\ message = [self \in replicaSet |-> ""]
        /\ toSend = [self \in replicaSet |-> {}]
        /\ replicaID = [self \in replicaSet |-> self]
        (* Process Client *)
        /\ clientID = "client"
        /\ leader \in chosenLeader
        /\ sending \in messageSet
        /\ pc = [self \in ProcSet |-> CASE self \in replicaSet -> "Broadcast"
                                        [] self = "client" -> "Send"]

Broadcast(self) == /\ pc[self] = "Broadcast"
                   /\ IF (chosenLeader = {self})
                         THEN /\ (sent_queue # <<>> /\ Head(sent_queue).to = self)
                              /\ message' = [message EXCEPT ![self] = Head(sent_queue).m]
                              /\ sent_queue' = Tail(sent_queue)
                              /\ toSend' = [toSend EXCEPT ![self] = replicaSet \ {self}]
                              /\ pc' = [pc EXCEPT ![self] = "BroadcastLoop"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "WaitForEcho"]
                              /\ UNCHANGED << sent_queue, message, toSend >>
                   /\ UNCHANGED << clientRequest, lastSent, replicaTerminated, 
                                   serverTerminated, sender, sentTo, 
                                   messageSet, globalSeqNum, msg_struct, 
                                   replicaID, clientID, leader, sending >>

BroadcastLoop(self) == /\ pc[self] = "BroadcastLoop"
                       /\ IF toSend[self] # {}
                             THEN /\ \E r \in toSend[self]:
                                       /\ globalSeqNum' = globalSeqNum + 1
                                       /\ msg_struct' = [m |-> message[self], sender |-> self, to |-> r, seq |-> globalSeqNum']
                                       /\ sent_queue' = Append(sent_queue, msg_struct')
                                       /\ toSend' = [toSend EXCEPT ![self] = toSend[self] \ {r}]
                                       /\ PrintT(<<"Replica " \o self \o " sent " \o msg_struct'.m \o " to " \o r \o ". Seq# -> " \o ToString(globalSeqNum')>>)
                                  /\ pc' = [pc EXCEPT ![self] = "BroadcastLoop"]
                                  /\ UNCHANGED replicaTerminated
                             ELSE /\ replicaTerminated' = [replicaTerminated EXCEPT ![self] = TRUE]
                                  /\ pc' = [pc EXCEPT ![self] = "WaitForEcho"]
                                  /\ UNCHANGED << sent_queue, globalSeqNum, 
                                                  msg_struct, toSend >>
                       /\ UNCHANGED << clientRequest, lastSent, 
                                       serverTerminated, sender, sentTo, 
                                       messageSet, message, replicaID, 
                                       clientID, leader, sending >>

WaitForEcho(self) == /\ pc[self] = "WaitForEcho"
                     /\ (sent_queue # <<>> /\ Head(sent_queue).to = self)
                     /\ sent_queue' = Tail(sent_queue)
                     /\ PrintT(<<"Sent Queue now: " \o ToString(Len(sent_queue'))>>)
                     /\ replicaTerminated' = [replicaTerminated EXCEPT ![self] = TRUE]
                     /\ pc' = [pc EXCEPT ![self] = "Done"]
                     /\ UNCHANGED << clientRequest, lastSent, serverTerminated, 
                                     sender, sentTo, messageSet, globalSeqNum, 
                                     msg_struct, message, toSend, replicaID, 
                                     clientID, leader, sending >>

Replica(self) == Broadcast(self) \/ BroadcastLoop(self)
                    \/ WaitForEcho(self)

Send == /\ pc["client"] = "Send"
        /\ globalSeqNum' = globalSeqNum + 1
        /\ msg_struct' = [m |-> sending, sender |-> clientID, to |-> leader, seq |-> globalSeqNum']
        /\ sent_queue' = Append(sent_queue, msg_struct')
        /\ PrintT(<<"Client message added to queue: message -> " \o msg_struct'.m \o ", sender -> "  \o msg_struct'.sender \o ", sequence# -> " \o ToString(msg_struct'.seq)>>)
        /\ PrintT(<<"Sent queue length: " \o ToString(Len(sent_queue'))>>)
        /\ pc' = [pc EXCEPT !["client"] = "Receive_all"]
        /\ UNCHANGED << clientRequest, lastSent, replicaTerminated, 
                        serverTerminated, sender, sentTo, messageSet, message, 
                        toSend, replicaID, clientID, leader, sending >>

Receive_all == /\ pc["client"] = "Receive_all"
               /\ PrintT(<<"Receiving">>)
               /\ pc' = [pc EXCEPT !["client"] = "ServerComplete"]
               /\ UNCHANGED << clientRequest, lastSent, replicaTerminated, 
                               serverTerminated, sent_queue, sender, sentTo, 
                               messageSet, globalSeqNum, msg_struct, message, 
                               toSend, replicaID, clientID, leader, sending >>

ServerComplete == /\ pc["client"] = "ServerComplete"
                  /\ PrintT(<<"Server echoed all available messages">>)
                  /\ serverTerminated' = TRUE
                  /\ pc' = [pc EXCEPT !["client"] = "Done"]
                  /\ UNCHANGED << clientRequest, lastSent, replicaTerminated, 
                                  sent_queue, sender, sentTo, messageSet, 
                                  globalSeqNum, msg_struct, message, toSend, 
                                  replicaID, clientID, leader, sending >>

Client == Send \/ Receive_all \/ ServerComplete

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Client
           \/ (\E self \in replicaSet: Replica(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Mon Nov 10 01:00:43 PST 2025 by daineyip
\* Created Mon Nov 10 00:59:31 PST 2025 by daineyip
