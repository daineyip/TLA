----------------------------- MODULE broadcast -----------------------------
\* TODO

EXTENDS Integers, Sequences, TLC

(* --algorithm echo

variables
clientRequest = "";
lastSent = "";
clientTerminated = FALSE;
clientSet = {"c1", "c2", "c3"};
chosenLeader = "c1"; \* Implement leader lock later
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
    TerminationCorrectness == SystemTermination => FALSE
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
        end if;
    WaitForEcho:
        await Len(sent_queue) = 2;
        print <<"Sent Queue: " \o ToString(Len(sent_queue))>>;
    clientTerminated := TRUE;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "1909b2e" /\ chksum(tla) = "e1a70e9b")
VARIABLES pc, clientRequest, lastSent, clientTerminated, clientSet, 
          chosenLeader, sent_queue, sender, sentTo, messageSet, globalSeqNum

(* define statement *)
SystemTermination == clientTerminated
TerminationCorrectness == SystemTermination => FALSE

VARIABLES sending, toSend, clientID, msg_struct

vars == << pc, clientRequest, lastSent, clientTerminated, clientSet, 
           chosenLeader, sent_queue, sender, sentTo, messageSet, globalSeqNum, 
           sending, toSend, clientID, msg_struct >>

ProcSet == (clientSet)

Init == (* Global variables *)
        /\ clientRequest = ""
        /\ lastSent = ""
        /\ clientTerminated = FALSE
        /\ clientSet = {"c1", "c2", "c3"}
        /\ chosenLeader = "c1"
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
                                   clientSet, chosenLeader, sent_queue, sender, 
                                   sentTo, messageSet, globalSeqNum, sending, 
                                   clientID, msg_struct >>

BroadcastLoop(self) == /\ pc[self] = "BroadcastLoop"
                       /\ IF toSend[self] # {}
                             THEN /\ \E c \in toSend[self]:
                                       /\ globalSeqNum' = globalSeqNum + 1
                                       /\ msg_struct' = [msg_struct EXCEPT ![self] = [m |-> sending[self], sender |-> self, to |-> c, seq |-> globalSeqNum']]
                                       /\ sent_queue' = Append(sent_queue, msg_struct'[self])
                                       /\ toSend' = [toSend EXCEPT ![self] = toSend[self] \ {c}]
                                       /\ PrintT(<<"Client " \o self \o " sent " \o msg_struct'[self].m \o " to " \o c \o ". Seq# -> " \o ToString(globalSeqNum')>>)
                                  /\ pc' = [pc EXCEPT ![self] = "BroadcastLoop"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "WaitForEcho"]
                                  /\ UNCHANGED << sent_queue, globalSeqNum, 
                                                  toSend, msg_struct >>
                       /\ UNCHANGED << clientRequest, lastSent, 
                                       clientTerminated, clientSet, 
                                       chosenLeader, sender, sentTo, 
                                       messageSet, sending, clientID >>

WaitForEcho(self) == /\ pc[self] = "WaitForEcho"
                     /\ Len(sent_queue) = 2
                     /\ PrintT(<<"Sent Queue: " \o ToString(Len(sent_queue))>>)
                     /\ clientTerminated' = TRUE
                     /\ pc' = [pc EXCEPT ![self] = "Done"]
                     /\ UNCHANGED << clientRequest, lastSent, clientSet, 
                                     chosenLeader, sent_queue, sender, sentTo, 
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
\* Last modified Tue Oct 21 16:24:33 PDT 2025 by daineyip
\* Created Tue Oct 21 15:11:32 PDT 2025 by daineyip
