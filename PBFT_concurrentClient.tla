----------------------- MODULE PBFT_concurrentClient -----------------------
EXTENDS Integers, Sequences, TLC, FiniteSets
CONSTANT replicaSet, chosenLeader, maxSeq, clientSet

(* --algorithm echo

variables
replicaTermination = [r \in replicaSet |-> FALSE];
clientTermination = [c \in clientSet |-> FALSE];
\*chosenLeader = "c1"; \* Implement leader lock later
inbox = [x \in (replicaSet \cup clientSet) |-> <<>>]; \*Client should be dynamically set
sender = "";
messageSet = {"m1"};
clientState = [c \in clientSet |-> "init"];
state = [r \in replicaSet |-> "init"];
received_log = [r \in replicaSet |-> {}];
client_log = [c \in clientSet |-> {}];

define
    ReplicaStates == {"init", "prepared", "committed", "done"}
    ClientStates == {"init", "done"}

    MessageTypes == {"preprepare", "prepare", "commit", "client_request", "client_response"}
    ReplicaOrClient == replicaSet \cup clientSet
    MessageSet == {"m1"}
    
    MessageRecords == [type: MessageTypes,
                       sender: ReplicaOrClient,
                       m: MessageSet,
                       seq: Nat,
                       to: ReplicaOrClient]

    TypeOK ==
        /\ inbox \in [ReplicaOrClient -> Seq(MessageRecords)]
        /\ replicaTermination \in [replicaSet -> BOOLEAN]
        /\ clientTermination \in [clientSet -> BOOLEAN]
        /\ state \in [replicaSet -> ReplicaStates]
        /\ received_log \in [replicaSet -> SUBSET MessageRecords]
        /\ clientState \in [clientSet -> ClientStates]
        /\ client_log \in [clientSet -> SUBSET MessageRecords]

    TerminationCorrectness == <>(\A r \in replicaSet : replicaTermination[r])

end define;

procedure Broadcast(from, msg, type, seqNum)
variables
toSend = replicaSet \ {from};
curr_msg = [m |-> "", sender |-> "", to |-> "", seq |-> 0, type |-> ""];
begin
    BroadcastLoop:
        while toSend # {} do
            with r \in toSend do
                curr_msg := [m |-> msg, sender |-> from, to |-> r, seq |-> seqNum, type |-> type];
                inbox[r] := Append(inbox[r], curr_msg);
                toSend := toSend \ {r};
                print <<"Replica " \o self \o " sent " \o curr_msg.m \o " to " \o r \o ". Seq# -> " \o ToString(seqNum) \o " | Type = " \o type>>;
            end with;
        end while;
    return;
end procedure;

fair process Replica \in replicaSet
variables
message = "";
toSend = {};
client = "";
next_seq = 1;
current_seq = 0;
curr_msg = [m |-> "", sender |-> "", to |-> "", seq |-> 0, type |-> ""];
req_state = [s \in 1..maxSeq |-> "init"];
begin
    MessageHandling:
        while state[self] # "done" do
            await inbox[self] # <<>>;
            curr_msg := Head(inbox[self]);
            inbox[self] := Tail(inbox[self]);
            
            received_log[self] := received_log[self] \cup {curr_msg};
            
            LeaderLogic:
                if (chosenLeader = {self} /\ curr_msg.type = "client_request") then
                    if next_seq <= maxSeq then
                    DoBroadcast:
                        call Broadcast(self, curr_msg.m, "preprepare", next_seq);
                        
                        SetStates:
                            req_state[next_seq] := "prepared";
\*                            received_log[self] := received_log[self] \cup {[m |-> msg_struct.m, sender |-> self, to |-> self, seq |-> next_seq, type |-> "prepare"]};
                            next_seq := next_seq + 1;
                    end if;
                end if;
            
            WaitForLeader:
                if curr_msg.seq > 0 then
                    current_seq := curr_msg.seq;
                        
                    Prepare:
                        if req_state[current_seq] = "init" /\ 
                            (\E m \in received_log[self] : m.type = "preprepare" /\ m.seq = current_seq) then
                            
                            PrePrepareBroadcast:
                                with m \in {x \in received_log[self] : x.type = "preprepare" /\ x.seq = current_seq} do
                                    call Broadcast(self, m.m, "prepare", current_seq);
                                end with;
                            
                            SetStatePrepared:
                                req_state[current_seq] := "prepared";
                                received_log[self] := received_log[self] \cup {[m |-> curr_msg.m, sender |-> self, to |-> self, seq |-> current_seq, type |-> "prepare"]};
                        end if;
                    
                    Commit:
                        if req_state[current_seq] = "prepared" /\
                            (Cardinality({m \in received_log[self] : (m.type = "prepare" \/ m.type = "preprepare") /\ m.seq = current_seq}) >= Cardinality(replicaSet)-1) then
                                PrepareBroadcast:
                                    with m \in {x \in received_log[self] : (x.type = "prepare" \/ x.type = "preprepare") /\ x.seq = current_seq} do
                                        call Broadcast(self, m.m, "commit", current_seq);
                                    end with;
                                    
                                SetStateCommitted:
                                    req_state[current_seq] := "committed";
                        end if ;
                    
                    RespondToClient:
                        if req_state[current_seq] = "committed" /\ 
                           (\E v \in MessageSet : 
                                Cardinality({m \in received_log[self] : m.type = "commit" /\ m.m = v /\ m.seq = current_seq}) >= Cardinality(replicaSet) - 1) 
                        then
                            with winning_val = CHOOSE v \in MessageSet : 
                                               Cardinality({m \in received_log[self] : m.type = "commit" /\ m.m = v /\ m.seq = current_seq}) >= Cardinality(replicaSet) - 1 
                            do
                                with c \in clientSet do
                                    curr_msg := [m |-> winning_val, 
                                                         sender |-> self, 
                                                         to |-> c,              \* <--- USE 'c' (VALID ID)
                                                         seq |-> current_seq, 
                                                         type |-> "client_response"];
                                                   
                                    inbox[c] := Append(inbox[c], curr_msg);
                                end with;
                                
                                
                                req_state[current_seq] := "done";
                                    
        \*                        replicaTermination[self] := TRUE;
                            end with;
                        end if;
                end if;
        end while; 
        
    Terminate:
        replicaTermination[self] := TRUE;  
end process;                    

fair process Client \in clientSet
variables
clientID = self;
\*leader \in chosenLeader;
leader = "r1";
sending \in messageSet;
threshold = Cardinality(replicaSet); \*2f+1 logic needed here
curr_msg = [m |-> "", sender |-> "", to |-> "", seq |-> 0, type |-> ""];
begin
    Send:
        curr_msg := [m |-> sending, sender |-> clientID, to |-> leader, seq |-> 0, type |-> "client_request"];
        inbox[leader] := Append(inbox[leader], curr_msg);
            
        print <<"Client message added to queue: message -> " \o curr_msg.m \o ", sender -> "  \o curr_msg.sender \o ", sequence# -> " \o ToString(curr_msg.seq)>>;
        print <<"Sent queue length: " \o ToString(Len(inbox[clientID]))>>;
            
    Receive_all:
        while clientState[self] # "done" do
            await inbox[self] # <<>>;
                curr_msg := Head(inbox[self]);
                inbox[self] := Tail(inbox[self]);
            
                client_log[self] := client_log[self] \cup {curr_msg};
            
            CompleteServer:
                if (Cardinality({m \in client_log[clientID] : m.type = "client_response"}) >= threshold) then
                    print <<"Server echoed all available messages (RECEIVED ALL COMMITS)">>;
                    clientState[self] := "done";
                    clientTermination[self] := TRUE;
                end if ; 
        end while;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "b0a3819e" /\ chksum(tla) = "bdcfe44d")
\* Process variable toSend of process Replica at line 66 col 1 changed to toSend_
\* Process variable curr_msg of process Replica at line 70 col 1 changed to curr_msg_
\* Process variable curr_msg of process Client at line 162 col 1 changed to curr_msg_C
CONSTANT defaultInitValue
VARIABLES pc, replicaTermination, clientTermination, inbox, sender, 
          messageSet, clientState, state, received_log, client_log, stack

(* define statement *)
ReplicaStates == {"init", "prepared", "committed", "done"}
ClientStates == {"init", "done"}

MessageTypes == {"preprepare", "prepare", "commit", "client_request", "client_response"}
ReplicaOrClient == replicaSet \cup clientSet
MessageSet == {"m1"}

MessageRecords == [type: MessageTypes,
                   sender: ReplicaOrClient,
                   m: MessageSet,
                   seq: Nat,
                   to: ReplicaOrClient]

TypeOK ==
    /\ inbox \in [ReplicaOrClient -> Seq(MessageRecords)]
    /\ replicaTermination \in [replicaSet -> BOOLEAN]
    /\ clientTermination \in [clientSet -> BOOLEAN]
    /\ state \in [replicaSet -> ReplicaStates]
    /\ received_log \in [replicaSet -> SUBSET MessageRecords]
    /\ clientState \in [clientSet -> ClientStates]
    /\ client_log \in [clientSet -> SUBSET MessageRecords]

TerminationCorrectness == <>(\A r \in replicaSet : replicaTermination[r])

VARIABLES from, msg, type, seqNum, toSend, curr_msg, message, toSend_, client, 
          next_seq, current_seq, curr_msg_, req_state, clientID, leader, 
          sending, threshold, curr_msg_C

vars == << pc, replicaTermination, clientTermination, inbox, sender, 
           messageSet, clientState, state, received_log, client_log, stack, 
           from, msg, type, seqNum, toSend, curr_msg, message, toSend_, 
           client, next_seq, current_seq, curr_msg_, req_state, clientID, 
           leader, sending, threshold, curr_msg_C >>

ProcSet == (replicaSet) \cup (clientSet)

Init == (* Global variables *)
        /\ replicaTermination = [r \in replicaSet |-> FALSE]
        /\ clientTermination = [c \in clientSet |-> FALSE]
        /\ inbox = [x \in (replicaSet \cup clientSet) |-> <<>>]
        /\ sender = ""
        /\ messageSet = {"m1"}
        /\ clientState = [c \in clientSet |-> "init"]
        /\ state = [r \in replicaSet |-> "init"]
        /\ received_log = [r \in replicaSet |-> {}]
        /\ client_log = [c \in clientSet |-> {}]
        (* Procedure Broadcast *)
        /\ from = [ self \in ProcSet |-> defaultInitValue]
        /\ msg = [ self \in ProcSet |-> defaultInitValue]
        /\ type = [ self \in ProcSet |-> defaultInitValue]
        /\ seqNum = [ self \in ProcSet |-> defaultInitValue]
        /\ toSend = [ self \in ProcSet |-> replicaSet \ {from[self]}]
        /\ curr_msg = [ self \in ProcSet |-> [m |-> "", sender |-> "", to |-> "", seq |-> 0, type |-> ""]]
        (* Process Replica *)
        /\ message = [self \in replicaSet |-> ""]
        /\ toSend_ = [self \in replicaSet |-> {}]
        /\ client = [self \in replicaSet |-> ""]
        /\ next_seq = [self \in replicaSet |-> 1]
        /\ current_seq = [self \in replicaSet |-> 0]
        /\ curr_msg_ = [self \in replicaSet |-> [m |-> "", sender |-> "", to |-> "", seq |-> 0, type |-> ""]]
        /\ req_state = [self \in replicaSet |-> [s \in 1..maxSeq |-> "init"]]
        (* Process Client *)
        /\ clientID = [self \in clientSet |-> self]
        /\ leader = [self \in clientSet |-> "r1"]
        /\ sending \in [clientSet -> messageSet]
        /\ threshold = [self \in clientSet |-> Cardinality(replicaSet)]
        /\ curr_msg_C = [self \in clientSet |-> [m |-> "", sender |-> "", to |-> "", seq |-> 0, type |-> ""]]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in replicaSet -> "MessageHandling"
                                        [] self \in clientSet -> "Send"]

BroadcastLoop(self) == /\ pc[self] = "BroadcastLoop"
                       /\ IF toSend[self] # {}
                             THEN /\ \E r \in toSend[self]:
                                       /\ curr_msg' = [curr_msg EXCEPT ![self] = [m |-> msg[self], sender |-> from[self], to |-> r, seq |-> seqNum[self], type |-> type[self]]]
                                       /\ inbox' = [inbox EXCEPT ![r] = Append(inbox[r], curr_msg'[self])]
                                       /\ toSend' = [toSend EXCEPT ![self] = toSend[self] \ {r}]
                                       /\ PrintT(<<"Replica " \o self \o " sent " \o curr_msg'[self].m \o " to " \o r \o ". Seq# -> " \o ToString(seqNum[self]) \o " | Type = " \o type[self]>>)
                                  /\ pc' = [pc EXCEPT ![self] = "BroadcastLoop"]
                                  /\ UNCHANGED << stack, from, msg, type, 
                                                  seqNum >>
                             ELSE /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                  /\ toSend' = [toSend EXCEPT ![self] = Head(stack[self]).toSend]
                                  /\ curr_msg' = [curr_msg EXCEPT ![self] = Head(stack[self]).curr_msg]
                                  /\ from' = [from EXCEPT ![self] = Head(stack[self]).from]
                                  /\ msg' = [msg EXCEPT ![self] = Head(stack[self]).msg]
                                  /\ type' = [type EXCEPT ![self] = Head(stack[self]).type]
                                  /\ seqNum' = [seqNum EXCEPT ![self] = Head(stack[self]).seqNum]
                                  /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                  /\ inbox' = inbox
                       /\ UNCHANGED << replicaTermination, clientTermination, 
                                       sender, messageSet, clientState, state, 
                                       received_log, client_log, message, 
                                       toSend_, client, next_seq, current_seq, 
                                       curr_msg_, req_state, clientID, leader, 
                                       sending, threshold, curr_msg_C >>

Broadcast(self) == BroadcastLoop(self)

MessageHandling(self) == /\ pc[self] = "MessageHandling"
                         /\ IF state[self] # "done"
                               THEN /\ inbox[self] # <<>>
                                    /\ curr_msg_' = [curr_msg_ EXCEPT ![self] = Head(inbox[self])]
                                    /\ inbox' = [inbox EXCEPT ![self] = Tail(inbox[self])]
                                    /\ received_log' = [received_log EXCEPT ![self] = received_log[self] \cup {curr_msg_'[self]}]
                                    /\ pc' = [pc EXCEPT ![self] = "LeaderLogic"]
                               ELSE /\ pc' = [pc EXCEPT ![self] = "Terminate"]
                                    /\ UNCHANGED << inbox, received_log, 
                                                    curr_msg_ >>
                         /\ UNCHANGED << replicaTermination, clientTermination, 
                                         sender, messageSet, clientState, 
                                         state, client_log, stack, from, msg, 
                                         type, seqNum, toSend, curr_msg, 
                                         message, toSend_, client, next_seq, 
                                         current_seq, req_state, clientID, 
                                         leader, sending, threshold, 
                                         curr_msg_C >>

LeaderLogic(self) == /\ pc[self] = "LeaderLogic"
                     /\ IF (chosenLeader = {self} /\ curr_msg_[self].type = "client_request")
                           THEN /\ IF next_seq[self] <= maxSeq
                                      THEN /\ pc' = [pc EXCEPT ![self] = "DoBroadcast"]
                                      ELSE /\ pc' = [pc EXCEPT ![self] = "WaitForLeader"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "WaitForLeader"]
                     /\ UNCHANGED << replicaTermination, clientTermination, 
                                     inbox, sender, messageSet, clientState, 
                                     state, received_log, client_log, stack, 
                                     from, msg, type, seqNum, toSend, curr_msg, 
                                     message, toSend_, client, next_seq, 
                                     current_seq, curr_msg_, req_state, 
                                     clientID, leader, sending, threshold, 
                                     curr_msg_C >>

DoBroadcast(self) == /\ pc[self] = "DoBroadcast"
                     /\ /\ from' = [from EXCEPT ![self] = self]
                        /\ msg' = [msg EXCEPT ![self] = curr_msg_[self].m]
                        /\ seqNum' = [seqNum EXCEPT ![self] = next_seq[self]]
                        /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Broadcast",
                                                                 pc        |->  "SetStates",
                                                                 toSend    |->  toSend[self],
                                                                 curr_msg  |->  curr_msg[self],
                                                                 from      |->  from[self],
                                                                 msg       |->  msg[self],
                                                                 type      |->  type[self],
                                                                 seqNum    |->  seqNum[self] ] >>
                                                             \o stack[self]]
                        /\ type' = [type EXCEPT ![self] = "preprepare"]
                     /\ toSend' = [toSend EXCEPT ![self] = replicaSet \ {from'[self]}]
                     /\ curr_msg' = [curr_msg EXCEPT ![self] = [m |-> "", sender |-> "", to |-> "", seq |-> 0, type |-> ""]]
                     /\ pc' = [pc EXCEPT ![self] = "BroadcastLoop"]
                     /\ UNCHANGED << replicaTermination, clientTermination, 
                                     inbox, sender, messageSet, clientState, 
                                     state, received_log, client_log, message, 
                                     toSend_, client, next_seq, current_seq, 
                                     curr_msg_, req_state, clientID, leader, 
                                     sending, threshold, curr_msg_C >>

SetStates(self) == /\ pc[self] = "SetStates"
                   /\ req_state' = [req_state EXCEPT ![self][next_seq[self]] = "prepared"]
                   /\ next_seq' = [next_seq EXCEPT ![self] = next_seq[self] + 1]
                   /\ pc' = [pc EXCEPT ![self] = "WaitForLeader"]
                   /\ UNCHANGED << replicaTermination, clientTermination, 
                                   inbox, sender, messageSet, clientState, 
                                   state, received_log, client_log, stack, 
                                   from, msg, type, seqNum, toSend, curr_msg, 
                                   message, toSend_, client, current_seq, 
                                   curr_msg_, clientID, leader, sending, 
                                   threshold, curr_msg_C >>

WaitForLeader(self) == /\ pc[self] = "WaitForLeader"
                       /\ IF curr_msg_[self].seq > 0
                             THEN /\ current_seq' = [current_seq EXCEPT ![self] = curr_msg_[self].seq]
                                  /\ pc' = [pc EXCEPT ![self] = "Prepare"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "MessageHandling"]
                                  /\ UNCHANGED current_seq
                       /\ UNCHANGED << replicaTermination, clientTermination, 
                                       inbox, sender, messageSet, clientState, 
                                       state, received_log, client_log, stack, 
                                       from, msg, type, seqNum, toSend, 
                                       curr_msg, message, toSend_, client, 
                                       next_seq, curr_msg_, req_state, 
                                       clientID, leader, sending, threshold, 
                                       curr_msg_C >>

Prepare(self) == /\ pc[self] = "Prepare"
                 /\ IF req_state[self][current_seq[self]] = "init" /\
                        (\E m \in received_log[self] : m.type = "preprepare" /\ m.seq = current_seq[self])
                       THEN /\ pc' = [pc EXCEPT ![self] = "PrePrepareBroadcast"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "Commit"]
                 /\ UNCHANGED << replicaTermination, clientTermination, inbox, 
                                 sender, messageSet, clientState, state, 
                                 received_log, client_log, stack, from, msg, 
                                 type, seqNum, toSend, curr_msg, message, 
                                 toSend_, client, next_seq, current_seq, 
                                 curr_msg_, req_state, clientID, leader, 
                                 sending, threshold, curr_msg_C >>

PrePrepareBroadcast(self) == /\ pc[self] = "PrePrepareBroadcast"
                             /\ \E m \in {x \in received_log[self] : x.type = "preprepare" /\ x.seq = current_seq[self]}:
                                  /\ /\ from' = [from EXCEPT ![self] = self]
                                     /\ msg' = [msg EXCEPT ![self] = m.m]
                                     /\ seqNum' = [seqNum EXCEPT ![self] = current_seq[self]]
                                     /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Broadcast",
                                                                              pc        |->  "SetStatePrepared",
                                                                              toSend    |->  toSend[self],
                                                                              curr_msg  |->  curr_msg[self],
                                                                              from      |->  from[self],
                                                                              msg       |->  msg[self],
                                                                              type      |->  type[self],
                                                                              seqNum    |->  seqNum[self] ] >>
                                                                          \o stack[self]]
                                     /\ type' = [type EXCEPT ![self] = "prepare"]
                                  /\ toSend' = [toSend EXCEPT ![self] = replicaSet \ {from'[self]}]
                                  /\ curr_msg' = [curr_msg EXCEPT ![self] = [m |-> "", sender |-> "", to |-> "", seq |-> 0, type |-> ""]]
                                  /\ pc' = [pc EXCEPT ![self] = "BroadcastLoop"]
                             /\ UNCHANGED << replicaTermination, 
                                             clientTermination, inbox, sender, 
                                             messageSet, clientState, state, 
                                             received_log, client_log, message, 
                                             toSend_, client, next_seq, 
                                             current_seq, curr_msg_, req_state, 
                                             clientID, leader, sending, 
                                             threshold, curr_msg_C >>

SetStatePrepared(self) == /\ pc[self] = "SetStatePrepared"
                          /\ req_state' = [req_state EXCEPT ![self][current_seq[self]] = "prepared"]
                          /\ received_log' = [received_log EXCEPT ![self] = received_log[self] \cup {[m |-> curr_msg_[self].m, sender |-> self, to |-> self, seq |-> current_seq[self], type |-> "prepare"]}]
                          /\ pc' = [pc EXCEPT ![self] = "Commit"]
                          /\ UNCHANGED << replicaTermination, 
                                          clientTermination, inbox, sender, 
                                          messageSet, clientState, state, 
                                          client_log, stack, from, msg, type, 
                                          seqNum, toSend, curr_msg, message, 
                                          toSend_, client, next_seq, 
                                          current_seq, curr_msg_, clientID, 
                                          leader, sending, threshold, 
                                          curr_msg_C >>

Commit(self) == /\ pc[self] = "Commit"
                /\ IF req_state[self][current_seq[self]] = "prepared" /\
                       (Cardinality({m \in received_log[self] : (m.type = "prepare" \/ m.type = "preprepare") /\ m.seq = current_seq[self]}) >= Cardinality(replicaSet)-1)
                      THEN /\ pc' = [pc EXCEPT ![self] = "PrepareBroadcast"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "RespondToClient"]
                /\ UNCHANGED << replicaTermination, clientTermination, inbox, 
                                sender, messageSet, clientState, state, 
                                received_log, client_log, stack, from, msg, 
                                type, seqNum, toSend, curr_msg, message, 
                                toSend_, client, next_seq, current_seq, 
                                curr_msg_, req_state, clientID, leader, 
                                sending, threshold, curr_msg_C >>

PrepareBroadcast(self) == /\ pc[self] = "PrepareBroadcast"
                          /\ \E m \in {x \in received_log[self] : (x.type = "prepare" \/ x.type = "preprepare") /\ x.seq = current_seq[self]}:
                               /\ /\ from' = [from EXCEPT ![self] = self]
                                  /\ msg' = [msg EXCEPT ![self] = m.m]
                                  /\ seqNum' = [seqNum EXCEPT ![self] = current_seq[self]]
                                  /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Broadcast",
                                                                           pc        |->  "SetStateCommitted",
                                                                           toSend    |->  toSend[self],
                                                                           curr_msg  |->  curr_msg[self],
                                                                           from      |->  from[self],
                                                                           msg       |->  msg[self],
                                                                           type      |->  type[self],
                                                                           seqNum    |->  seqNum[self] ] >>
                                                                       \o stack[self]]
                                  /\ type' = [type EXCEPT ![self] = "commit"]
                               /\ toSend' = [toSend EXCEPT ![self] = replicaSet \ {from'[self]}]
                               /\ curr_msg' = [curr_msg EXCEPT ![self] = [m |-> "", sender |-> "", to |-> "", seq |-> 0, type |-> ""]]
                               /\ pc' = [pc EXCEPT ![self] = "BroadcastLoop"]
                          /\ UNCHANGED << replicaTermination, 
                                          clientTermination, inbox, sender, 
                                          messageSet, clientState, state, 
                                          received_log, client_log, message, 
                                          toSend_, client, next_seq, 
                                          current_seq, curr_msg_, req_state, 
                                          clientID, leader, sending, threshold, 
                                          curr_msg_C >>

SetStateCommitted(self) == /\ pc[self] = "SetStateCommitted"
                           /\ req_state' = [req_state EXCEPT ![self][current_seq[self]] = "committed"]
                           /\ pc' = [pc EXCEPT ![self] = "RespondToClient"]
                           /\ UNCHANGED << replicaTermination, 
                                           clientTermination, inbox, sender, 
                                           messageSet, clientState, state, 
                                           received_log, client_log, stack, 
                                           from, msg, type, seqNum, toSend, 
                                           curr_msg, message, toSend_, client, 
                                           next_seq, current_seq, curr_msg_, 
                                           clientID, leader, sending, 
                                           threshold, curr_msg_C >>

RespondToClient(self) == /\ pc[self] = "RespondToClient"
                         /\ IF req_state[self][current_seq[self]] = "committed" /\
                               (\E v \in MessageSet :
                                    Cardinality({m \in received_log[self] : m.type = "commit" /\ m.m = v /\ m.seq = current_seq[self]}) >= Cardinality(replicaSet) - 1)
                               THEN /\ LET winning_val == CHOOSE v \in MessageSet :
                                                          Cardinality({m \in received_log[self] : m.type = "commit" /\ m.m = v /\ m.seq = current_seq[self]}) >= Cardinality(replicaSet) - 1 IN
                                         /\ \E c \in clientSet:
                                              /\ curr_msg_' = [curr_msg_ EXCEPT ![self] = [m |-> winning_val,
                                                                                                   sender |-> self,
                                                                                                   to |-> c,
                                                                                                   seq |-> current_seq[self],
                                                                                                   type |-> "client_response"]]
                                              /\ inbox' = [inbox EXCEPT ![c] = Append(inbox[c], curr_msg_'[self])]
                                         /\ req_state' = [req_state EXCEPT ![self][current_seq[self]] = "done"]
                               ELSE /\ TRUE
                                    /\ UNCHANGED << inbox, curr_msg_, 
                                                    req_state >>
                         /\ pc' = [pc EXCEPT ![self] = "MessageHandling"]
                         /\ UNCHANGED << replicaTermination, clientTermination, 
                                         sender, messageSet, clientState, 
                                         state, received_log, client_log, 
                                         stack, from, msg, type, seqNum, 
                                         toSend, curr_msg, message, toSend_, 
                                         client, next_seq, current_seq, 
                                         clientID, leader, sending, threshold, 
                                         curr_msg_C >>

Terminate(self) == /\ pc[self] = "Terminate"
                   /\ replicaTermination' = [replicaTermination EXCEPT ![self] = TRUE]
                   /\ pc' = [pc EXCEPT ![self] = "Done"]
                   /\ UNCHANGED << clientTermination, inbox, sender, 
                                   messageSet, clientState, state, 
                                   received_log, client_log, stack, from, msg, 
                                   type, seqNum, toSend, curr_msg, message, 
                                   toSend_, client, next_seq, current_seq, 
                                   curr_msg_, req_state, clientID, leader, 
                                   sending, threshold, curr_msg_C >>

Replica(self) == MessageHandling(self) \/ LeaderLogic(self)
                    \/ DoBroadcast(self) \/ SetStates(self)
                    \/ WaitForLeader(self) \/ Prepare(self)
                    \/ PrePrepareBroadcast(self) \/ SetStatePrepared(self)
                    \/ Commit(self) \/ PrepareBroadcast(self)
                    \/ SetStateCommitted(self) \/ RespondToClient(self)
                    \/ Terminate(self)

Send(self) == /\ pc[self] = "Send"
              /\ curr_msg_C' = [curr_msg_C EXCEPT ![self] = [m |-> sending[self], sender |-> clientID[self], to |-> leader[self], seq |-> 0, type |-> "client_request"]]
              /\ inbox' = [inbox EXCEPT ![leader[self]] = Append(inbox[leader[self]], curr_msg_C'[self])]
              /\ PrintT(<<"Client message added to queue: message -> " \o curr_msg_C'[self].m \o ", sender -> "  \o curr_msg_C'[self].sender \o ", sequence# -> " \o ToString(curr_msg_C'[self].seq)>>)
              /\ PrintT(<<"Sent queue length: " \o ToString(Len(inbox'[clientID[self]]))>>)
              /\ pc' = [pc EXCEPT ![self] = "Receive_all"]
              /\ UNCHANGED << replicaTermination, clientTermination, sender, 
                              messageSet, clientState, state, received_log, 
                              client_log, stack, from, msg, type, seqNum, 
                              toSend, curr_msg, message, toSend_, client, 
                              next_seq, current_seq, curr_msg_, req_state, 
                              clientID, leader, sending, threshold >>

Receive_all(self) == /\ pc[self] = "Receive_all"
                     /\ IF clientState[self] # "done"
                           THEN /\ inbox[self] # <<>>
                                /\ curr_msg_C' = [curr_msg_C EXCEPT ![self] = Head(inbox[self])]
                                /\ inbox' = [inbox EXCEPT ![self] = Tail(inbox[self])]
                                /\ client_log' = [client_log EXCEPT ![self] = client_log[self] \cup {curr_msg_C'[self]}]
                                /\ pc' = [pc EXCEPT ![self] = "CompleteServer"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                /\ UNCHANGED << inbox, client_log, curr_msg_C >>
                     /\ UNCHANGED << replicaTermination, clientTermination, 
                                     sender, messageSet, clientState, state, 
                                     received_log, stack, from, msg, type, 
                                     seqNum, toSend, curr_msg, message, 
                                     toSend_, client, next_seq, current_seq, 
                                     curr_msg_, req_state, clientID, leader, 
                                     sending, threshold >>

CompleteServer(self) == /\ pc[self] = "CompleteServer"
                        /\ IF (Cardinality({m \in client_log[clientID[self]] : m.type = "client_response"}) >= threshold[self])
                              THEN /\ PrintT(<<"Server echoed all available messages (RECEIVED ALL COMMITS)">>)
                                   /\ clientState' = [clientState EXCEPT ![self] = "done"]
                                   /\ clientTermination' = [clientTermination EXCEPT ![self] = TRUE]
                              ELSE /\ TRUE
                                   /\ UNCHANGED << clientTermination, 
                                                   clientState >>
                        /\ pc' = [pc EXCEPT ![self] = "Receive_all"]
                        /\ UNCHANGED << replicaTermination, inbox, sender, 
                                        messageSet, state, received_log, 
                                        client_log, stack, from, msg, type, 
                                        seqNum, toSend, curr_msg, message, 
                                        toSend_, client, next_seq, current_seq, 
                                        curr_msg_, req_state, clientID, leader, 
                                        sending, threshold, curr_msg_C >>

Client(self) == Send(self) \/ Receive_all(self) \/ CompleteServer(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet: Broadcast(self))
           \/ (\E self \in replicaSet: Replica(self))
           \/ (\E self \in clientSet: Client(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in replicaSet : WF_vars(Replica(self)) /\ WF_vars(Broadcast(self))
        /\ \A self \in clientSet : WF_vars(Client(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Fri Dec 19 13:43:29 MST 2025 by daineyip
\* Created Mon Dec 08 23:44:08 PST 2025 by daineyip
