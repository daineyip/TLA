----------------------------- MODULE broadcast -----------------------------
\* This is a basic broadcast protocol
\* Capable of handling an arbitrary number of clients, and a chosen leader
\* Chosen leader node sends a message "m1" to all replicas besides itself, the replicas receive the message and remove it from the sent_queue

EXTENDS Integers, Sequences, TLC
CONSTANT clientSet, chosenLeader

(* --algorithm echo

variables
clientRequest = "";
lastSent = "";
clientTerminated = [c \in clientSet |-> FALSE];
\*chosenLeader = "c1"; \* Implement leader lock later
sent_queue = <<>>;
sender = "";
sentTo = "";
messageSet = {"m1"};
globalSeqNum = 0;

define
\*    CorrectnessInvariant ==
\*        /\ (serverResponse # "" /\ lastSent # "") =>
\*           (serverResponse = lastSent) \* This will fail with 2 rounds
    SystemTermination == clientTerminated
\*    TerminationCorrectness == SystemTermination => FALSE
       TerminationCorrectness == <>(\A c \in clientSet : clientTerminated[c])

\*      TerminationCorrectness == clientTerminated

end define;

process Client \in clientSet
variables
sending \in messageSet;
toSend = {};
clientID = self;
msg_struct = [m |-> "", sender |-> "", to |-> "", seq |-> 0];
\* local memory for last sent
begin
    Broadcast:
        if (chosenLeader = clientID) then
            toSend := clientSet \ {self};
            BroadcastLoop:
                while toSend # {} do
                    with c \in toSend do
                        globalSeqNum := globalSeqNum + 1;
                        msg_struct := [m |-> sending, sender |-> self, to |-> c, seq |-> globalSeqNum];
                        sent_queue := Append(sent_queue, msg_struct);
                        toSend := toSend \ {c};
                        print <<"Client " \o self \o " sent " \o msg_struct.m \o " to " \o c \o ". Seq# -> " \o ToString(globalSeqNum)>>;
                    end with;
                end while;
            clientTerminated[self] := TRUE;
        end if;
    WaitForEcho:
        await (sent_queue # <<>> /\ Head(sent_queue).to = self);
        sent_queue := Tail(sent_queue);
        print <<"Sent Queue now: " \o ToString(Len(sent_queue))>>;
    clientTerminated[self] := TRUE;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "b2507f5c" /\ chksum(tla) = "1cd13f3e")
VARIABLES pc, clientRequest, lastSent, clientTerminated, sent_queue, sender, 
          sentTo, messageSet, globalSeqNum

(* define statement *)
SystemTermination == clientTerminated

   TerminationCorrectness == <>(\A c \in clientSet : clientTerminated[c])

VARIABLES sending, toSend, clientID, msg_struct

vars == << pc, clientRequest, lastSent, clientTerminated, sent_queue, sender, 
           sentTo, messageSet, globalSeqNum, sending, toSend, clientID, 
           msg_struct >>

ProcSet == (clientSet)

Init == (* Global variables *)
        /\ clientRequest = ""
        /\ lastSent = ""
        /\ clientTerminated = [c \in clientSet |-> FALSE]
        /\ sent_queue = <<>>
        /\ sender = ""
        /\ sentTo = ""
        /\ messageSet = {"m1"}
        /\ globalSeqNum = 0
        (* Process Client *)
        /\ sending \in [clientSet -> messageSet]
        /\ toSend = [self \in clientSet |-> {}]
        /\ clientID = [self \in clientSet |-> self]
        /\ msg_struct = [self \in clientSet |-> [m |-> "", sender |-> "", to |-> "", seq |-> 0]]
        /\ pc = [self \in ProcSet |-> "Broadcast"]

Broadcast(self) == /\ pc[self] = "Broadcast"
                   /\ IF (chosenLeader = clientID[self])
                         THEN /\ toSend' = [toSend EXCEPT ![self] = clientSet \ {self}]
                              /\ pc' = [pc EXCEPT ![self] = "BroadcastLoop"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "WaitForEcho"]
                              /\ UNCHANGED toSend
                   /\ UNCHANGED << clientRequest, lastSent, clientTerminated, 
                                   sent_queue, sender, sentTo, messageSet, 
                                   globalSeqNum, sending, clientID, msg_struct >>

BroadcastLoop(self) == /\ pc[self] = "BroadcastLoop"
                       /\ IF toSend[self] # {}
                             THEN /\ \E c \in toSend[self]:
                                       /\ globalSeqNum' = globalSeqNum + 1
                                       /\ msg_struct' = [msg_struct EXCEPT ![self] = [m |-> sending[self], sender |-> self, to |-> c, seq |-> globalSeqNum']]
                                       /\ sent_queue' = Append(sent_queue, msg_struct'[self])
                                       /\ toSend' = [toSend EXCEPT ![self] = toSend[self] \ {c}]
                                       /\ PrintT(<<"Client " \o self \o " sent " \o msg_struct'[self].m \o " to " \o c \o ". Seq# -> " \o ToString(globalSeqNum')>>)
                                  /\ pc' = [pc EXCEPT ![self] = "BroadcastLoop"]
                                  /\ UNCHANGED clientTerminated
                             ELSE /\ clientTerminated' = [clientTerminated EXCEPT ![self] = TRUE]
                                  /\ pc' = [pc EXCEPT ![self] = "WaitForEcho"]
                                  /\ UNCHANGED << sent_queue, globalSeqNum, 
                                                  toSend, msg_struct >>
                       /\ UNCHANGED << clientRequest, lastSent, sender, sentTo, 
                                       messageSet, sending, clientID >>

WaitForEcho(self) == /\ pc[self] = "WaitForEcho"
                     /\ (sent_queue # <<>> /\ Head(sent_queue).to = self)
                     /\ sent_queue' = Tail(sent_queue)
                     /\ PrintT(<<"Sent Queue now: " \o ToString(Len(sent_queue'))>>)
                     /\ clientTerminated' = [clientTerminated EXCEPT ![self] = TRUE]
                     /\ pc' = [pc EXCEPT ![self] = "Done"]
                     /\ UNCHANGED << clientRequest, lastSent, sender, sentTo, 
                                     messageSet, globalSeqNum, sending, toSend, 
                                     clientID, msg_struct >>

Client(self) == Broadcast(self) \/ BroadcastLoop(self) \/ WaitForEcho(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in clientSet: Client(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Wed Oct 22 22:53:09 PDT 2025 by daineyip
\* Created Tue Oct 21 15:11:32 PDT 2025 by daineyip
