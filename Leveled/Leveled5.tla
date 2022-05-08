---- MODULE Leveled5 ----

EXTENDS TLC, FiniteSets, Sequences, Naturals
\* keys and values of LedgerCache in Bookie
CONSTANTS LedC_Vals, LedC_Keys
ASSUME Cardinality(LedC_Keys) = Cardinality(LedC_Vals)
\* keys and values of Manifest in Penciller and Inker
\* CONSTANTS Man_Keys, Man_Vals
\* ASSUME Cardinality(Man_Keys) = Cardinality(Man_Vals)

\* converts sequence to set
Range(seq) == {seq[x] : x \in seq}
\* find max value in set
Max(set) == CHOOSE item \in set:
    \A other \in set: item >= other
\* get last element of the sequence
Last(seq) == seq[Len(seq)]

Message(from, to, op_type) == [from |-> from, to |-> to, op |-> op_type]

Messages ==
         Message("usr", "bok", "put")
    \cup Message("bok", "ink", "put")

VARIABLES
    ink_state, \* state of the Inker actor process
    bok_state, \* state of the Bookie actor process
    msgs_usr,  \* messages that the user sends to the system
    msgs_send, \* map to seq of messages that each actor process sends
    msgs_recv, \* map to set of received messages for each actor process
    sys_state  \* status of the system

vars == <<msgs_send, msgs_recv, sys_state, msgs_usr, ink_state, bok_state>>

Init ==
    /\ msgs_usr = <<Message("usr", "bok", "put")>>
    /\ sys_state = "active"
    /\ msgs_send = [actor \in {"ink", "bok", "pen"} |-> <<>>]
    /\ msgs_recv = [actor \in {"ink", "bok", "pen"} |-> {}]
    /\ bok_state = [
        ledger_cache |-> [LedC_Keys -> LedC_Vals]]
    /\ ink_state = [
        is_snapshot |-> FALSE,
        journal_sqn |-> 0,
        manifest_sqn |-> 0]
    \* /\ ink_state = [
    \*     manifest |-> [journal |-> <<>>, active |-> 1],
    \*     manifest_sqn |-> 0]

TypeInv ==
    /\ sys_state \in {"active", "done"}
    /\ msgs_usr \in SUBSET Messages
    /\ msgs_send \in SUBSET Messages
    /\ msgs_recv \in SUBSET Messages
    /\ bok_state.ledger_cache \in [LedC_Keys -> LedC_Vals]

    /\ ink_state.journal_sqn \in Nat
    /\ ink_state.manifest_sqn \in Nat
    /\ ink_state.is_snapshot \in BOOLEAN
    \* /\ \A journal_id \in Range(ink_state.manifest):
    \*         journal_id \in Nat
    \* /\ ink_state.manifest_sqn \in Nat

Usr_SendPut ==
    /\ msgs_usr # <<>>
    /\
        LET
            msg == Head(msgs_usr)
        IN
            /\ msg.op = "put"

            /\ msgs_recv' = [msgs_recv EXCEPT !["bok"] = @ \cup {msg}]
            /\ msgs_usr' = Tail(msgs_usr)
    /\ UNCHANGED <<sys_state, msgs_send, ink_state, bok_state>>

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
    /\ UNCHANGED <<sys_state, msgs_usr, ink_state, bok_state>>

Ink_RecvPutBok ==
    /\ \E r_msg \in msgs_recv["ink"]:
        /\ r_msg.from = "bok" /\ r_msg.to = "ink" /\ r_msg.op = "put"
        /\ msgs_recv' = [msgs_recv EXCEPT !["ink"] = @ \ {r_msg}]

        /\ ink_state.is_snapshot = FALSE

        /\ \E journal_file_cap \in {"full", "not_full"}:
                /\ CASE
                    journal_file_cap = "full" -> \* roll the file
                        ink_state' = [ink_state EXCEPT
                            !["journal_sqn"] = @ + 1,
                            !["manifest_sqn"] = @ + 1]
                    [] journal_file_cap = "not_full" ->
                        ink_state' = [ink_state EXCEPT
                            !["journal_sqn"] = @ + 1]
        /\ sys_state' = "done"
    /\ UNCHANGED  <<msgs_send, msgs_usr, bok_state>>

Terminated ==
    /\ sys_state = "done"
    /\ UNCHANGED vars

Next ==
    \/ Usr_SendPut
    \/ Bok_RecvPutUsr
    \/ Ink_RecvPutBok
    \/ Terminated

\* check property is sequential
====
