---- MODULE Leveled4 ----

EXTENDS TLC, FiniteSets, Sequences, Naturals

\* converts sequence to set
Range(seq) == { seq[x] : x \in seq }

\* messages that the user sends
\* CONSTANT msgs_usr
\* ASSUME Len(msgs_usr) > 0
\* ASSUME (\A msg \in Range(msgs_usr):
            \* /\ msg.from = "usr"
            \* /\ msg.to = "bok"
            \* /\ msg.op \in {"put"})

Message(from, to, op_type) == [from |-> from, to |-> to, op |-> op_type]

Messages ==
         Message("usr", "bok", "put")
    \cup Message("bok", "ink", "put") 

VARIABLES
    msgs_usr,  \* messages that the user sends to the system
    msgs_send, \* map to seq of messages that each actor process sends
    msgs_recv, \* map to set of received messages for each actor process
    sys_state  \* status of the system

vars == <<msgs_send, msgs_recv, sys_state, msgs_usr>>

Init ==
    /\ msgs_usr = <<Message("usr", "bok", "put")>>
    /\ sys_state = "active"
    /\ msgs_send = [actor \in {"ink", "bok", "pen"} |-> <<>>]
    /\ msgs_recv = [actor \in {"ink", "bok", "pen"} |-> {}]

TypeInv ==
    /\ sys_state \in {"active", "done"}
    /\ msgs_usr \in SUBSET Messages
    /\ msgs_send \in SUBSET Messages
    /\ msgs_recv \in SUBSET Messages

Usr_SendPut ==
    /\ msgs_usr # <<>>
    /\ 
        LET 
            msg == Head(msgs_usr)
        IN 
            /\ msg.op = "put"

            /\ msgs_recv' = [msgs_recv EXCEPT !["bok"] = @ \cup {msg}]
            /\ msgs_usr' = Tail(msgs_usr)
    /\ UNCHANGED <<sys_state, msgs_send>>

Bok_RecvPutUsr ==    
    /\ \E r_msg \in msgs_recv["bok"]:
        /\ r_msg.from = "usr" /\ r_msg.to = "bok" /\ r_msg.op = "put" 
        /\ 
            LET 
                s_msg == Message("bok", "ink", "put")
            IN
                /\ msgs_recv' = [msgs_recv EXCEPT 
                    !["ink"] = @ \cup {s_msg},
                    !["bok"] = @ \ {r_msg}]
                /\ msgs_send' = [msgs_send EXCEPT !["bok"] = Append(@, s_msg)]
    /\ UNCHANGED <<sys_state, msgs_usr>>

Ink_RecvPutBok ==
    /\ \E r_msg \in msgs_recv["ink"]:
        /\ r_msg.from = "bok" /\ r_msg.to = "ink" /\ r_msg.op = "put"
        /\ msgs_recv' = [msgs_recv EXCEPT !["ink"] = @ \ {r_msg}] 
        /\ sys_state' = "done"
    /\ UNCHANGED  <<msgs_send, msgs_usr>>

Terminated ==
    /\ sys_state = "done"
    /\ UNCHANGED vars

Next == 
    \/ Usr_SendPut
    \/ Bok_RecvPutUsr
    \/ Ink_RecvPutBok
    \/ Terminated
====