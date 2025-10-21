-------------------------------- MODULE echo_multimessage --------------------------------

\* This is a single-sender, single-server echo implementation.
\* Capable of the client sending arbitrary amount of string n messages in messageSet, to the server, and successfully receiving n echos where m'_n = m_n

EXTENDS Integers, Sequences, TLC, FiniteSets
CONSTANT messageSet

(* --algorithm echo

variables
sentMsg \in messageSet;
clientTerminated = FALSE;
serverTerminated = FALSE;
messages_left = Cardinality(messageSet); \* Turn this into dynamic
messagesToHandle = Cardinality(messageSet); \* Very non-elegant
send_queue = <<>>;
received_queue = <<>>;
latest_serverResponse = [m |-> "", s |-> "", seq |-> 0];
latest_messageSent = [m |-> "", s |-> "", seq |-> 0];
globalSeqNum = 0;
clientSet = {"c1"};

define
    CorrectnessInvariant ==
        (latest_serverResponse.seq # 0 
        /\ latest_messageSent.seq # 0 
        /\ latest_messageSent.seq = latest_serverResponse.seq) =>
            (latest_messageSent = latest_serverResponse)
    
    
    SystemTermination == 
        clientTerminated /\ serverTerminated
    
    TerminationCorrectness == 
        SystemTermination => 
            (latest_messageSent = latest_serverResponse 
             /\ latest_messageSent # [m |-> "", s |-> "", seq |-> 0])
    
    QueueCorrectness == 
        SystemTermination => 
            (Len(send_queue) = 0 /\ Len(received_queue) = 0)
end define;

process Client \in clientSet
variables
sending \in messageSet;
clientID = self;
expected = <<>>;
received_msg = [m |-> "", s |-> "", seq |-> 0];
begin
    ClientLoop:
        while (messagesToHandle > 0 \/ messages_left > 0 \/ received_queue # <<>>) do
            Send:
                if (messages_left > 0) then
                    globalSeqNum := globalSeqNum + 1;
                   
                    with msg_struct = [m |-> sending, s |-> clientID, seq |-> globalSeqNum] do
                        expected := Append(expected, globalSeqNum);
                        send_queue := Append(send_queue, msg_struct);
                        
                        latest_messageSent := msg_struct; \* For Correctness Invariant
        
                        messages_left := messages_left - 1; \* Better logic later
                        
                        print <<"Client message added to queue: message -> " \o msg_struct.m \o ", sender -> "  \o msg_struct.s \o ", sequence# -> " \o ToString(msg_struct.seq)>>;
                        print <<"Send queue length: " \o ToString(Len(send_queue))>>
                        
                    end with;
                end if;
            ReadFromQueue:
                if (received_queue # <<>> /\ Head(received_queue).seq \in {expected[i] : i \in 1..Len(expected)}) then
                    received_msg := Head(received_queue);
                    received_queue := Tail(received_queue);
                    expected := SelectSeq(expected, LAMBDA x: x /= received_msg.seq);
                    messagesToHandle := messagesToHandle - 1;
                    print <<"Echo received by Client: " \o received_msg.m \o " from " \o received_msg.s \o ". Seq# -> " \o ToString(received_msg.seq)>>;
                    print <<"Received queue after read: " \o ToString(Len(received_queue))>>;
                end if;
        end while;
    clientTerminated := TRUE;
end process;

process Server = "server"
begin
    ServerLoop:
        while messagesToHandle > 0 do
            WaitForRequest:
                await send_queue # <<>>;
                print <<"Server has message in queue", Head(send_queue)>>;
                print <<"messages_left: ", messagesToHandle>>;
            Echo:
                received_queue := Append(received_queue, Head(send_queue));
                latest_serverResponse := Head(send_queue);
                print <<"Server sent back", Head(send_queue)>>;
                send_queue := Tail(send_queue);
        end while;
    ServerComplete:
        print <<"Server echoed all available messages">>;
        serverTerminated := TRUE;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "cf997a41" /\ chksum(tla) = "bbf9fbc4")
VARIABLES pc, sentMsg, clientTerminated, serverTerminated, messages_left, 
          messagesToHandle, send_queue, received_queue, latest_serverResponse, 
          latest_messageSent, globalSeqNum, clientSet

(* define statement *)
CorrectnessInvariant ==
    (latest_serverResponse.seq # 0
    /\ latest_messageSent.seq # 0
    /\ latest_messageSent.seq = latest_serverResponse.seq) =>
        (latest_messageSent = latest_serverResponse)


SystemTermination ==
    clientTerminated /\ serverTerminated

TerminationCorrectness ==
    SystemTermination =>
        (latest_messageSent = latest_serverResponse
         /\ latest_messageSent # [m |-> "", s |-> "", seq |-> 0])

QueueCorrectness ==
    SystemTermination =>
        (Len(send_queue) = 0 /\ Len(received_queue) = 0)

VARIABLES sending, clientID, expected, received_msg

vars == << pc, sentMsg, clientTerminated, serverTerminated, messages_left, 
           messagesToHandle, send_queue, received_queue, 
           latest_serverResponse, latest_messageSent, globalSeqNum, clientSet, 
           sending, clientID, expected, received_msg >>

ProcSet == (clientSet) \cup {"server"}

Init == (* Global variables *)
        /\ sentMsg \in messageSet
        /\ clientTerminated = FALSE
        /\ serverTerminated = FALSE
        /\ messages_left = Cardinality(messageSet)
        /\ messagesToHandle = Cardinality(messageSet)
        /\ send_queue = <<>>
        /\ received_queue = <<>>
        /\ latest_serverResponse = [m |-> "", s |-> "", seq |-> 0]
        /\ latest_messageSent = [m |-> "", s |-> "", seq |-> 0]
        /\ globalSeqNum = 0
        /\ clientSet = {"c1"}
        (* Process Client *)
        /\ sending \in [clientSet -> messageSet]
        /\ clientID = [self \in clientSet |-> self]
        /\ expected = [self \in clientSet |-> <<>>]
        /\ received_msg = [self \in clientSet |-> [m |-> "", s |-> "", seq |-> 0]]
        /\ pc = [self \in ProcSet |-> CASE self \in clientSet -> "ClientLoop"
                                        [] self = "server" -> "ServerLoop"]

ClientLoop(self) == /\ pc[self] = "ClientLoop"
                    /\ IF (messagesToHandle > 0 \/ messages_left > 0 \/ received_queue # <<>>)
                          THEN /\ pc' = [pc EXCEPT ![self] = "Send"]
                               /\ UNCHANGED clientTerminated
                          ELSE /\ clientTerminated' = TRUE
                               /\ pc' = [pc EXCEPT ![self] = "Done"]
                    /\ UNCHANGED << sentMsg, serverTerminated, messages_left, 
                                    messagesToHandle, send_queue, 
                                    received_queue, latest_serverResponse, 
                                    latest_messageSent, globalSeqNum, 
                                    clientSet, sending, clientID, expected, 
                                    received_msg >>

Send(self) == /\ pc[self] = "Send"
              /\ IF (messages_left > 0)
                    THEN /\ globalSeqNum' = globalSeqNum + 1
                         /\ LET msg_struct == [m |-> sending[self], s |-> clientID[self], seq |-> globalSeqNum'] IN
                              /\ expected' = [expected EXCEPT ![self] = Append(expected[self], globalSeqNum')]
                              /\ send_queue' = Append(send_queue, msg_struct)
                              /\ latest_messageSent' = msg_struct
                              /\ messages_left' = messages_left - 1
                              /\ PrintT(<<"Client message added to queue: message -> " \o msg_struct.m \o ", sender -> "  \o msg_struct.s \o ", sequence# -> " \o ToString(msg_struct.seq)>>)
                              /\ PrintT(<<"Send queue length: " \o ToString(Len(send_queue'))>>)
                    ELSE /\ TRUE
                         /\ UNCHANGED << messages_left, send_queue, 
                                         latest_messageSent, globalSeqNum, 
                                         expected >>
              /\ pc' = [pc EXCEPT ![self] = "ReadFromQueue"]
              /\ UNCHANGED << sentMsg, clientTerminated, serverTerminated, 
                              messagesToHandle, received_queue, 
                              latest_serverResponse, clientSet, sending, 
                              clientID, received_msg >>

ReadFromQueue(self) == /\ pc[self] = "ReadFromQueue"
                       /\ IF (received_queue # <<>> /\ Head(received_queue).seq \in {expected[self][i] : i \in 1..Len(expected[self])})
                             THEN /\ received_msg' = [received_msg EXCEPT ![self] = Head(received_queue)]
                                  /\ received_queue' = Tail(received_queue)
                                  /\ expected' = [expected EXCEPT ![self] = SelectSeq(expected[self], LAMBDA x: x /= received_msg'[self].seq)]
                                  /\ messagesToHandle' = messagesToHandle - 1
                                  /\ PrintT(<<"Echo received by Client: " \o received_msg'[self].m \o " from " \o received_msg'[self].s \o ". Seq# -> " \o ToString(received_msg'[self].seq)>>)
                                  /\ PrintT(<<"Received queue after read: " \o ToString(Len(received_queue'))>>)
                             ELSE /\ TRUE
                                  /\ UNCHANGED << messagesToHandle, 
                                                  received_queue, expected, 
                                                  received_msg >>
                       /\ pc' = [pc EXCEPT ![self] = "ClientLoop"]
                       /\ UNCHANGED << sentMsg, clientTerminated, 
                                       serverTerminated, messages_left, 
                                       send_queue, latest_serverResponse, 
                                       latest_messageSent, globalSeqNum, 
                                       clientSet, sending, clientID >>

Client(self) == ClientLoop(self) \/ Send(self) \/ ReadFromQueue(self)

ServerLoop == /\ pc["server"] = "ServerLoop"
              /\ IF messagesToHandle > 0
                    THEN /\ pc' = [pc EXCEPT !["server"] = "WaitForRequest"]
                    ELSE /\ pc' = [pc EXCEPT !["server"] = "ServerComplete"]
              /\ UNCHANGED << sentMsg, clientTerminated, serverTerminated, 
                              messages_left, messagesToHandle, send_queue, 
                              received_queue, latest_serverResponse, 
                              latest_messageSent, globalSeqNum, clientSet, 
                              sending, clientID, expected, received_msg >>

WaitForRequest == /\ pc["server"] = "WaitForRequest"
                  /\ send_queue # <<>>
                  /\ PrintT(<<"Server has message in queue", Head(send_queue)>>)
                  /\ PrintT(<<"messages_left: ", messagesToHandle>>)
                  /\ pc' = [pc EXCEPT !["server"] = "Echo"]
                  /\ UNCHANGED << sentMsg, clientTerminated, serverTerminated, 
                                  messages_left, messagesToHandle, send_queue, 
                                  received_queue, latest_serverResponse, 
                                  latest_messageSent, globalSeqNum, clientSet, 
                                  sending, clientID, expected, received_msg >>

Echo == /\ pc["server"] = "Echo"
        /\ received_queue' = Append(received_queue, Head(send_queue))
        /\ latest_serverResponse' = Head(send_queue)
        /\ PrintT(<<"Server sent back", Head(send_queue)>>)
        /\ send_queue' = Tail(send_queue)
        /\ pc' = [pc EXCEPT !["server"] = "ServerLoop"]
        /\ UNCHANGED << sentMsg, clientTerminated, serverTerminated, 
                        messages_left, messagesToHandle, latest_messageSent, 
                        globalSeqNum, clientSet, sending, clientID, expected, 
                        received_msg >>

ServerComplete == /\ pc["server"] = "ServerComplete"
                  /\ PrintT(<<"Server echoed all available messages">>)
                  /\ serverTerminated' = TRUE
                  /\ pc' = [pc EXCEPT !["server"] = "Done"]
                  /\ UNCHANGED << sentMsg, clientTerminated, messages_left, 
                                  messagesToHandle, send_queue, received_queue, 
                                  latest_serverResponse, latest_messageSent, 
                                  globalSeqNum, clientSet, sending, clientID, 
                                  expected, received_msg >>

Server == ServerLoop \/ WaitForRequest \/ Echo \/ ServerComplete

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
\* Last modified Mon Oct 20 23:17:55 PDT 2025 by daineyip
\* Created Tue Sep 23 19:42:59 PDT 2025 by daineyip
