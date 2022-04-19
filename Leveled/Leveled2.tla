---- MODULE Leveled2 ----
EXTENDS TLC, FiniteSets, Sequences
VARIABLES
    \* sequence of messages sent to the system
    usr_msgs,
    \* messages that the process has sent
    msg_sqs,
    \* messages that the process has received
    msg_rqs,
    \* state of the system
    pc
vars == <<msg_sqs, msg_rqs, usr_msgs, pc>>
ProcType_Pen == "Pen"
ProcType_Ink == "Ink"
ProcType_Bok == "Bok"
User == "User"
PC_Started == "Started"
PC_Done == "Done"
Processes == {ProcType_Pen, ProcType_Ink, ProcType_Bok}
MessageSenders == User \cup Processes
OpType_Put == "PUT"
Operations == {OpType_Put}
PutPayload(key, value) == [
    key   |-> key,
    value |-> value
]
Message(src, dst, op_type, payload) == [
    src     |-> src,
    dst     |-> dst,
    op      |-> op_type,
    payload |-> payload
]
PutMessage(key, value) == Message(User, ProcType_Bok, OpType_Put, PutPayload(key, value))
NewPutMsgFromMsg(msg, src, dst) == Message(src, dst, OpType_Put, PutPayload(msg.payload.key, msg.payload.value)) 
Usr_SendPut ==
    /\  usr_msgs # <<>>
    /\  LET msg == Head(usr_msgs)
        IN
            /\ msg.op = OpType_Put
            
            /\  LET 
                    src == User
                    dst == ProcType_Bok
                    smsg == NewPutMsgFromMsg(msg, src, dst)
                IN
                    /\ msg_rqs' = [msg_rqs EXCEPT ![dst] = @ \cup {smsg}]
                    /\ msg_sqs' = 
                        IF src = User THEN msg_sqs
                        ELSE [msg_sqs EXCEPT ![src] = Append(@, smsg)]
                    /\ usr_msgs' = Tail(usr_msgs)
    /\ UNCHANGED <<pc>>

Bok_RecvPut ==
    /\  \E msg \in msg_rqs[ProcType_Bok]: 
            /\ msg.op = OpType_Put
            
            /\  LET
                    src == ProcType_Bok
                    dst == ProcType_Ink
                    smsg == NewPutMsgFromMsg(msg, src, dst)
                IN
                    /\ msg_rqs' = [msg_rqs EXCEPT 
                        ![dst] = @ \cup {smsg},
                        ![src] = @ \ {msg}]
                    /\ msg_sqs' = [msg_sqs EXCEPT ![src] = Append(@, smsg)]
                    /\ pc' = PC_Done
    /\ UNCHANGED <<usr_msgs>>

Terminating ==
    /\ pc = PC_Done
    /\ UNCHANGED vars

RECURSIVE SeqToSetInt(_, _)
SeqToSetInt(seq, set) ==
    IF seq = <<>> THEN set
    ELSE SeqToSetInt(Tail(seq), set \cup {Head(seq)})
SeqToSet(seq) == SeqToSetInt(seq, {})

TypeInv ==
    /\  DOMAIN msg_sqs \cup DOMAIN msg_rqs \subseteq Processes
    /\  \A p \in Processes:
            /\  LET msgs == SeqToSet(msg_sqs[p]) \cup msg_rqs[p]
                IN \A msg \in msgs:
                    /\ msg.src \in Processes \cup {User}
                    /\ msg.dst \in Processes
                    /\ msg.op  \in Operations

Init ==
    /\ pc = PC_Started
    /\ msg_sqs = [p \in Processes |-> <<>>]
    /\ msg_rqs = [p \in Processes |-> {}]

Next ==
    \/ Usr_SendPut
    \/ Bok_RecvPut
    \/ Terminating
====