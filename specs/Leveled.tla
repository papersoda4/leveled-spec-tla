---- MODULE Leveled ----

EXTENDS TLC, FiniteSets, Sequences, Naturals
\* keys and values of LedgerCache in Bookie
CONSTANTS LedC_Vals, LedC_Keys
ASSUME Cardinality(LedC_Keys) = Cardinality(LedC_Vals)

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
    (*control*)
    sys_state, \* current status of the system
    pc,        \* current status for each of the actors
    (*messages*)
    msgs_usr,  \* messages that the user sends to the system
    msgs_send, \* map to seq of messages that each actor process sends
    msgs_recv, \* map to set of received messages for each actor process
    (*process state*)
    ink_state, \* state of the Inker actor process
    bok_state \* state of the Bookie actor process

vars == <<msgs_send, msgs_recv, sys_state, msgs_usr, ink_state, bok_state, pc>>

Init ==
    (*control*)
    /\ sys_state = "active"
    /\ pc = [actor \in {"ink", "bok", "pen"} |-> "init"]
    (*messages*)
    /\ msgs_usr = <<Message("usr", "bok", "put")>>
    /\ msgs_send = [actor \in {"ink", "bok", "pen"} |-> <<>>]
    /\ msgs_recv = [actor \in {"ink", "bok", "pen"} |-> {}]
    (*process state*)
    /\ bok_state = [
        ledger_cache |-> [LedC_Keys -> LedC_Vals]]
    /\ ink_state = [
        manifest |-> [sqn \in {0, 1, 2} |-> <<>>],
        is_snapshot |-> FALSE,
        journal_sqn |-> 0,
        manifest_sqn |-> 2]

TypeInv ==
    (*control*)
    /\ sys_state \in {"active", "done"}
    /\ pc
        \in  [{"ink"} -> {"init", "put_recv", "put_roll_active_journal", "put_write"}]
        \cup [{"bok"} -> {"init"}]
        \cup [{"pen"} -> {"init"}]
    (*messages*)
    /\ msgs_usr \in SUBSET Messages
    /\ msgs_send \in SUBSET Messages
    /\ msgs_recv \in SUBSET Messages
    (*process state*)
    \* bookie
    /\ bok_state.ledger_cache \in [LedC_Keys -> LedC_Vals]
    \* inker
    /\ ink_state.journal_sqn \in Nat
    /\ ink_state.manifest_sqn \in Nat
    /\ ink_state.is_snapshot \in BOOLEAN
    /\ ink_state.active_journal \in Nat

Usr_SendPut ==
    /\ msgs_usr # <<>>
    /\
        LET
            msg == Head(msgs_usr)
        IN
            /\ msg.op = "put"

            /\ msgs_recv' = [msgs_recv EXCEPT !["bok"] = @ \cup {msg}]
            /\ msgs_usr' = Tail(msgs_usr)
    /\ UNCHANGED <<sys_state, msgs_send, ink_state, bok_state, pc>>

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
    /\ UNCHANGED <<sys_state, msgs_usr, ink_state, bok_state, pc>>

Ink_RecvPutBok ==
    /\ pc["ink"] = "init"
    /\ \E r_msg \in msgs_recv["ink"]:
        /\ r_msg.from = "bok" /\ r_msg.to = "ink" /\ r_msg.op = "put"
        /\ msgs_recv' = [msgs_recv EXCEPT !["ink"] = @ \ {r_msg}]
        /\ pc' = [pc EXCEPT !["ink"] = "put_recv"]
    /\ UNCHANGED <<msgs_send, sys_state, msgs_usr, bok_state, ink_state>>
Ink_ProcPutBok ==
    /\ pc["ink"] = "put_recv"
    /\ ink_state.is_snapshot = FALSE

    /\ \E journal_file_cap \in {"full", "not_full"}:
        /\ CASE
            journal_file_cap = "full" ->
                pc' = [pc EXCEPT !["ink"] = "put_roll_active_journal"]
            [] journal_file_cap = "not_full" ->
                pc' = [pc EXCEPT !["ink"] = "put_write"]
    /\ UNCHANGED <<msgs_send, msgs_recv, sys_state, msgs_usr, bok_state, ink_state>>
Ink_RollActiveJournal ==
    /\ pc["ink"] = "put_roll_active_journal"

    /\ ink_state' = [ink_state EXCEPT
         !["manifest"] =
            (ink_state.manifest_sqn + 1 :> <<>>)
            @@ ink_state.manifest,
         !["journal_sqn"] = @ + 1,
         !["manifest_sqn"] = @ + 1]
    /\ pc' = [pc EXCEPT !["ink"] = "put_write"]
    /\ UNCHANGED <<msgs_send, sys_state, msgs_recv, msgs_usr, bok_state>>
Ink_PutWrite ==
    /\ pc["ink"] = "put_write"

    /\ ink_state' = [ink_state EXCEPT
         !["manifest"] = [ink_state.manifest EXCEPT
             ![ink_state.manifest_sqn] =
                Append(
                    ink_state.manifest[ink_state.manifest_sqn],
                    <<ink_state.journal_sqn, "val">>)],
         !["journal_sqn"] = @ + 1]
    /\ pc' = [pc EXCEPT !["ink"] = "init"]
    /\ sys_state' = "done"
    /\ UNCHANGED  <<msgs_send, msgs_recv, msgs_usr, bok_state>>
Ink_PutValueToJournal ==
    \/ Ink_RecvPutBok
    \/ Ink_ProcPutBok
    \/ Ink_RollActiveJournal
    \/ Ink_PutWrite

Terminated ==
    /\ sys_state = "done"
    /\ UNCHANGED vars

Next ==
    \/ Usr_SendPut
    \/ Bok_RecvPutUsr
    \/ Ink_PutValueToJournal
    \/ Terminated

====