-------------------------------- MODULE echo --------------------------------

\* This is a single-sender, single-server echo implementation.
\* Capable of the client sending a string m, to the server, and successfully receiving an echo m' where m' = m

EXTENDS Integers, Sequences, TLC
\*CONSTANT messageSet, clientSet

(* --algorithm echo

variables
clientRequest = "";
serverResponse = "";
lastSent = "";
clientTerminated = FALSE;
serverTerminated = FALSE;
sender = "";
sentTo = "";
clientSet = {"c1"};
messageSet = {"m1"};

define
    CorrectnessInvariant ==
        /\ (serverResponse # "" /\ lastSent # "") =>
           (serverResponse = lastSent) \* This will fail with 2 rounds
    SystemTermination == clientTerminated /\ serverTerminated
    TerminationCorrectness == SystemTermination => (lastSent = serverResponse /\ lastSent # "")
end define;

process Client \in clientSet
variables
sending \in messageSet;
clientID = self;
\* local memory for last sent
begin
    SendMessage:
        lastSent := sending;
        clientRequest := sending;
        sender := clientID;
        print <<"Client message sent: " \o sending \o " from " \o sender>>;
    WaitForEcho:
        await serverResponse # "" /\ sentTo = clientID;
        print <<"Echo received by Client: " \o serverResponse>>;
        clientTerminated := TRUE;
end process;

process Server = "server"
begin
    WaitForRequest:
        await clientRequest # "";
        print <<"Server received Client message: " \o clientRequest>>;
    Echo:
        sentTo := sender;
        serverResponse := clientRequest;
        print <<"Server responded back to Client " \o sender \o " with response: " \o serverResponse>>;
        serverTerminated := TRUE;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "15ac377d" /\ chksum(tla) = "53349b70")
VARIABLES pc, clientRequest, serverResponse, lastSent, clientTerminated, 
          serverTerminated, sender, sentTo, clientSet, messageSet

(* define statement *)
CorrectnessInvariant ==
    /\ (serverResponse # "" /\ lastSent # "") =>
       (serverResponse = lastSent)
SystemTermination == clientTerminated /\ serverTerminated
TerminationCorrectness == SystemTermination => (lastSent = serverResponse /\ lastSent # "")

VARIABLES sending, clientID

vars == << pc, clientRequest, serverResponse, lastSent, clientTerminated, 
           serverTerminated, sender, sentTo, clientSet, messageSet, sending, 
           clientID >>

ProcSet == (clientSet) \cup {"server"}

Init == (* Global variables *)
        /\ clientRequest = ""
        /\ serverResponse = ""
        /\ lastSent = ""
        /\ clientTerminated = FALSE
        /\ serverTerminated = FALSE
        /\ sender = ""
        /\ sentTo = ""
        /\ clientSet = {"c1"}
        /\ messageSet = {"m1"}
        (* Process Client *)
        /\ sending \in [clientSet -> messageSet]
        /\ clientID = [self \in clientSet |-> self]
        /\ pc = [self \in ProcSet |-> CASE self \in clientSet -> "SendMessage"
                                        [] self = "server" -> "WaitForRequest"]

SendMessage(self) == /\ pc[self] = "SendMessage"
                     /\ lastSent' = sending[self]
                     /\ clientRequest' = sending[self]
                     /\ sender' = clientID[self]
                     /\ PrintT(<<"Client message sent: " \o sending[self] \o " from " \o sender'>>)
                     /\ pc' = [pc EXCEPT ![self] = "WaitForEcho"]
                     /\ UNCHANGED << serverResponse, clientTerminated, 
                                     serverTerminated, sentTo, clientSet, 
                                     messageSet, sending, clientID >>

WaitForEcho(self) == /\ pc[self] = "WaitForEcho"
                     /\ serverResponse # "" /\ sentTo = clientID[self]
                     /\ PrintT(<<"Echo received by Client: " \o serverResponse>>)
                     /\ clientTerminated' = TRUE
                     /\ pc' = [pc EXCEPT ![self] = "Done"]
                     /\ UNCHANGED << clientRequest, serverResponse, lastSent, 
                                     serverTerminated, sender, sentTo, 
                                     clientSet, messageSet, sending, clientID >>

Client(self) == SendMessage(self) \/ WaitForEcho(self)

WaitForRequest == /\ pc["server"] = "WaitForRequest"
                  /\ clientRequest # ""
                  /\ PrintT(<<"Server received Client message: " \o clientRequest>>)
                  /\ pc' = [pc EXCEPT !["server"] = "Echo"]
                  /\ UNCHANGED << clientRequest, serverResponse, lastSent, 
                                  clientTerminated, serverTerminated, sender, 
                                  sentTo, clientSet, messageSet, sending, 
                                  clientID >>

Echo == /\ pc["server"] = "Echo"
        /\ sentTo' = sender
        /\ serverResponse' = clientRequest
        /\ PrintT(<<"Server responded back to Client " \o sender \o " with response: " \o serverResponse'>>)
        /\ serverTerminated' = TRUE
        /\ pc' = [pc EXCEPT !["server"] = "Done"]
        /\ UNCHANGED << clientRequest, lastSent, clientTerminated, sender, 
                        clientSet, messageSet, sending, clientID >>

Server == WaitForRequest \/ Echo

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Server
           \/ (\E self \in clientSet: Client(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 


=============================================================================
\* Modification History
\* Last modified Mon Oct 20 20:44:40 PDT 2025 by daineyip
\* Created Tue Sep 23 19:42:59 PDT 2025 by daineyip
