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
IsSortedSeq(seq) ==
    /\ seq # <<>>
    /\ \A i \in 1..Len(seq):
        \A j \in 1..Len(seq):
           /\ i # j
           /\ i \leq j
                => seq[i] \leq seq[j]

Message(from, to, op_type) == [from |-> from, to |-> to, op |-> op_type]

Messages ==
         Message("usr", "bok", "put")
    \cup Message("bok", "ink", "put")
    \cup Message("ink", "bok", "put")
    \cup Message("bok", "pen", "put")
    \cup Message("pen", "bok", "put")
    \cup Message("usr", "bok", "get")
    \cup Message("bok", "pen", "get")
    \cup Message("pen", "bok", "get")
    \cup Message("bok", "ink", "get")
    \cup Message("ink", "bok", "get")
    \cup Message("bok", "usr", "put")

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
    bok_state, \* state of the Bookie actor process
    pen_state  \* state of the Penciller actor process

vars == <<msgs_send, msgs_recv, sys_state, msgs_usr, ink_state, bok_state, pc, pen_state>>

Init ==
    (*control*)
    /\ sys_state = "active"
    /\ pc = [actor \in {"ink", "bok", "pen"} |-> "init"]
    (*messages*)
    /\ msgs_usr = <<Message("usr", "bok", "put"), Message("usr", "bok", "get")>>
    /\ msgs_send = [actor \in {"ink", "bok", "pen"} |-> <<>>]
    /\ msgs_recv = [actor \in {"ink", "bok", "pen"} \cup {"usr"} |-> {}]
    (*process state*)
    /\ bok_state = [
        ledger_cache |-> [LedC_Keys -> LedC_Vals]]
    /\ ink_state = [
        manifest |-> [sqn \in {0, 1, 2} |-> <<>>],
        is_snapshot |-> FALSE,
        journal_sqn |-> 0,
        manifest_sqn |-> 2]
    /\ pen_state = [
        is_snapshot |-> FALSE,
        memory |-> <<>>]

TypeInv ==
    (*control*)
    /\ sys_state \in {"active", "done"}
    /\ pc
        \in  [{"ink"} -> {
            "init", "put_recv", "put_roll_active_journal", "put_write", "put_send_changes"}]
        \cup [{"bok"} ->
            {"init"}
            \cup {"put_recv", "put_wait_ink", "put_ledger_cache", "put_push_mem",
            "put_wait_push_mem", "put_recv_push_mem", "put_send_usr", "put_try_pushmem"}
            \cup {"get_recv"}]
        \cup [{"pen"} -> {
            "init", "put_recv", "put_push_ok", "put_push_ret", "put_cache_full",
            "put_cache_busy", "put_push_mem"}]
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
    \* penciller
    /\ pen_state.is_snapshot \in BOOLEAN

Usr_SendPut ==
    /\ msgs_usr # <<>>
    /\
        LET
            msg == Head(msgs_usr)
        IN
            /\ msg.op = "put"

            /\ msgs_recv' = [msgs_recv EXCEPT !["bok"] = @ \cup {msg}]
            /\ msgs_usr' = Tail(msgs_usr)
    /\ UNCHANGED <<sys_state, msgs_send, ink_state, bok_state, pc, pen_state>>
Usr_SendGet ==
    /\ msgs_usr # <<>>
    /\
        LET
            msg == Head(msgs_usr)
        IN
            /\ msg.op = "get"

            /\ msgs_recv' = [msgs_recv EXCEPT !["bok"] = @ \cup {msg}]
            /\ msgs_usr' = Tail(msgs_usr)
    /\ UNCHANGED <<sys_state, msgs_send, ink_state, bok_state, pc, pen_state>>

Bok_RecvPutUsr ==
    /\ sys_state # "done"
    /\ pc["bok"] = "init"
    /\ \E msg \in msgs_recv["bok"]:
        /\ msg.from = "usr" /\ msg.to = "bok" /\ msg.op = "put"
            /\ msgs_recv' = [msgs_recv EXCEPT !["bok"] = @ \ {msg}]
            /\ pc' = [pc EXCEPT !["bok"] = "recv_put"]
    /\ UNCHANGED <<sys_state, msgs_usr, ink_state, bok_state, msgs_send, pen_state>>
Bok_SendWriteToJournal ==
    /\ sys_state # "done"
    /\ pc["bok"] = "recv_put"
    /\
        LET
            msg == Message("bok", "ink", "put")
        IN
            /\ msgs_recv' = [msgs_recv EXCEPT !["ink"] = @ \cup {msg}]
            /\ msgs_send' = [msgs_send EXCEPT !["bok"] = Append(@, msg)]
            /\ pc' = [pc EXCEPT !["bok"] = "put_wait_ink"]
    /\ UNCHANGED <<sys_state, msgs_usr, ink_state, bok_state, pen_state>>
Bok_RecvJournalChanges ==
    /\ sys_state # "done"
    /\ pc["bok"] = "put_wait_ink"
    /\ \E msg \in msgs_recv["bok"]:
        /\ msg.from = "ink" /\ msg.to = "bok" /\ msg.op = "put"
        /\ msgs_recv' = [msgs_recv EXCEPT !["bok"] = @ \ {msg}]
        /\ pc' = [pc EXCEPT !["bok"] = "put_ledger_cache"]
    /\ UNCHANGED <<msgs_usr, ink_state, bok_state, msgs_send, sys_state, pen_state>>
Bok_AddToLedgerCache ==
    /\ sys_state # "done"
    /\ pc["bok"] = "put_ledger_cache"
    /\ bok_state' = [bok_state EXCEPT !["ledger_cache"] = {x @@ ("k3" :> "v3"): x \in @}]
    /\ pc' = [pc EXCEPT !["bok"] = "put_send_usr"]
    /\ UNCHANGED <<msgs_usr, ink_state, msgs_send, msgs_recv, sys_state, pen_state>>
Bok_PutSendUsr ==
    /\ sys_state # "done"
    /\ pc["bok"] = "put_send_usr"
    /\
        LET
            msg == Message("bok", "usr", "put")
        IN
            /\ msgs_recv' = [msgs_recv EXCEPT !["usr"] = @ \cup {msg}]
            /\ msgs_send' = [msgs_send EXCEPT !["bok"] = Append(@, msg)]
            /\ pc' = [pc EXCEPT !["bok"] = "put_try_pushmem"]
    /\ UNCHANGED <<msgs_usr, ink_state, bok_state, pen_state, sys_state>>

(*
    background process 'push_mem'
    writes LedgerCache of Bookie to Penciller
    - LedgerCache contains most recent changes
    'push_mem' process is executed if
    - Penciller is not busy, depending on last sync (backpressure)
    - LedgerCache has reached a certain capacity (has n amount of entries written)
*)
Bok_CheckPushMemReady ==
    /\ sys_state # "done"
    /\ pc["bok"] = "put_try_pushmem"
    /\ \E cache_large_enough \in {TRUE, FALSE}:
        IF cache_large_enough THEN
            /\ pc' = [pc EXCEPT !["bok"] = "put_push_mem"]
            /\ UNCHANGED <<sys_state, msgs_usr, msgs_send, msgs_recv, pen_state, ink_state, bok_state>>
        ELSE
            /\ sys_state' = "done"
            /\ UNCHANGED <<pc, msgs_usr, msgs_send, msgs_recv, pen_state, ink_state, bok_state>>

\* Bok_CheckPenBusy ==
\*     \E penciller_is_busy \in {TRUE, FALSE}:
\*         IF penciller_is_busy THEN

Bok_SendPushMemPen ==
    /\ sys_state # "done"
    /\ pc["bok"] = "put_push_mem"
    /\
        LET
            msg == Message("bok", "pen", "put")
        IN
            /\ msgs_recv' = [msgs_recv EXCEPT !["pen"] = @ \cup {msg}]
            /\ msgs_send' = [msgs_send EXCEPT !["bok"] = Append(@, msg)]
            /\ pc' = [pc EXCEPT !["bok"] = "put_wait_push_mem"]
    /\ UNCHANGED <<msgs_usr, ink_state, bok_state, ink_state, sys_state, pen_state>>
Bok_RecvPushMemOk ==
    /\ sys_state # "done"
    /\ pc["bok"] = "put_wait_push_mem"
    /\ \E msg \in msgs_recv["bok"]:
        /\ msg.from = "pen" /\ msg.to = "bok" /\ msg.op = "put"
        /\ msgs_recv' = [msgs_recv EXCEPT !["bok"] = @ \ {msg}]
        /\ pc' = [pc EXCEPT !["bok"] = "put_recv_push_mem"]
    /\ UNCHANGED <<msgs_usr, ink_state, msgs_send, sys_state, bok_state, pen_state>>
Bok_CleanCache ==
    /\ sys_state # "done"
    /\ pc["bok"] = "put_recv_push_mem"
    /\ bok_state' = [bok_state EXCEPT !["ledger_cache"] = {}]
    /\ sys_state' = "done"
    /\ UNCHANGED <<msgs_usr, msgs_send, msgs_recv, pen_state, ink_state, pc>>

Pen_RecvPushmemBok ==
    /\ sys_state # "done"
    /\ pc["pen"] = "init"
    /\ pen_state.is_snapshot = FALSE
    /\ \E msg \in msgs_recv["pen"]:
        /\ msg.from = "bok" /\ msg.to = "pen" /\ msg.op = "put"
        /\ msgs_recv' = [msgs_recv EXCEPT !["pen"] = @ \ {msg}]
        /\ pc' = [pc EXCEPT !["pen"] = "put_recv"]
    /\ UNCHANGED <<msgs_send, sys_state, msgs_usr, bok_state, ink_state, pen_state>>
Pen_ProcPushmemBok ==
    /\ sys_state # "done"
    /\ pc["pen"] = "put_recv"
    /\ \E cache_blocked_by_pending_work \in {TRUE, FALSE}:
            IF cache_blocked_by_pending_work THEN
                pc' = [pc EXCEPT !["pen"] = "put_cache_busy"]
            ELSE
                \E cache_is_full \in {TRUE, FALSE}:
                    IF cache_is_full THEN
                        pc' = [pc EXCEPT !["pen"] = "put_cache_full"]
                    ELSE
                        pc' = [pc EXCEPT !["pen"] = "put_push_mem"]
    /\ UNCHANGED <<msgs_send, sys_state, msgs_usr, bok_state, ink_state, msgs_recv, pen_state>>
Pen_RetryPushLaterBok ==
    /\ sys_state # "done"
    /\ pc["pen"] = "put_cache_busy"
    /\ pc' = [pc EXCEPT !["pen"] = "put_push_ret"]
    /\ UNCHANGED <<msgs_send, sys_state, msgs_usr, bok_state, ink_state, msgs_recv, pen_state>>
Pen_RollMemory ==
    /\ sys_state # "done"
    /\ pc["pen"] = "put_cache_full"
    /\ pc' = [pc EXCEPT !["pen"] = "put_push_ret"]
    /\ UNCHANGED <<msgs_send, sys_state, msgs_usr, bok_state, ink_state, msgs_recv, pen_state>>
Pen_Push ==
    /\ sys_state # "done"
    /\ pc["pen"] = "put_push_mem"
    /\ pen_state' = [pen_state EXCEPT !["memory"] = Append(@, "val")]
    /\ pc' = [pc EXCEPT !["pen"] = "put_push_ok"]
    /\ UNCHANGED <<msgs_send, sys_state, msgs_usr, bok_state, ink_state, msgs_recv>>
Pen_SendPushmemBok ==
    /\ sys_state # "done"
    /\
        \/ pc["pen"] = "put_push_ret"
        \/ pc["pen"] = "put_push_ok"
    /\
        LET
            msg == Message("pen", "bok", "put")
        IN
            /\ msgs_recv' = [msgs_recv EXCEPT !["bok"] = @ \cup {msg}]
            /\ msgs_send' = [msgs_send EXCEPT !["pen"] = Append(@, msg)]
            /\ pc' = [pc EXCEPT !["pen"] = "init"]
    /\ UNCHANGED <<msgs_usr, ink_state, bok_state, ink_state, sys_state, pen_state>>

Ink_RecvWriteReqBok ==
    /\ sys_state # "done"
    /\ pc["ink"] = "init"
    /\ \E msg \in msgs_recv["ink"]:
        /\ msg.from = "bok" /\ msg.to = "ink" /\ msg.op = "put"
        /\ msgs_recv' = [msgs_recv EXCEPT !["ink"] = @ \ {msg}]
        /\ pc' = [pc EXCEPT !["ink"] = "put_recv"]
    /\ UNCHANGED <<msgs_send, sys_state, msgs_usr, bok_state, ink_state, pen_state>>
Ink_CheckCanWrite ==
    /\ sys_state # "done"
    /\ pc["ink"] = "put_recv"
    /\ ink_state.is_snapshot = FALSE

    /\ \E journal_file_cap \in {"full", "not_full"}:
        /\ CASE
            journal_file_cap = "full" ->
                pc' = [pc EXCEPT !["ink"] = "put_roll_active_journal"]
            [] journal_file_cap = "not_full" ->
                pc' = [pc EXCEPT !["ink"] = "put_write"]
    /\ UNCHANGED <<msgs_send, msgs_recv, sys_state, msgs_usr, bok_state, ink_state, pen_state>>
Ink_RollActiveJournal ==
    /\ sys_state # "done"
    /\ pc["ink"] = "put_roll_active_journal"

    /\ ink_state' = [ink_state EXCEPT
         !["manifest"] =
            (ink_state.manifest_sqn + 1 :> <<>>)
            @@ ink_state.manifest,
         !["journal_sqn"] = @ + 1,
         !["manifest_sqn"] = @ + 1]
    /\ pc' = [pc EXCEPT !["ink"] = "put_write"]
    /\ UNCHANGED <<msgs_send, sys_state, msgs_recv, msgs_usr, bok_state, pen_state>>
Ink_WriteValueToJournal ==
    /\ sys_state # "done"
    /\ pc["ink"] = "put_write"

    /\ ink_state' = [ink_state EXCEPT
         !["manifest"] = [ink_state.manifest EXCEPT
             ![ink_state.manifest_sqn] =
                Append(
                    ink_state.manifest[ink_state.manifest_sqn],
                    <<ink_state.journal_sqn, "val">>)],
         !["journal_sqn"] = @ + 1]
    /\ pc' = [pc EXCEPT !["ink"] = "put_send_changes"]
    /\ UNCHANGED  <<msgs_usr, bok_state, sys_state, msgs_send, msgs_recv, pen_state>>
Ink_SendChangesToBok ==
    /\ sys_state # "done"
    /\ pc["ink"] = "put_send_changes"
    /\  LET
            msg == Message("ink", "bok", "put")
        IN
            /\ msgs_recv' = [msgs_recv EXCEPT !["bok"] = @ \cup {msg}]
            /\ msgs_send' = [msgs_send EXCEPT !["ink"] = Append(@, msg)]
            /\ pc' = [pc EXCEPT !["ink"] = "init"]
    /\ UNCHANGED  <<msgs_usr, bok_state, sys_state, ink_state, pen_state>>

Bok_RecvGetUsr ==
    /\ sys_state # "done"
    /\ pc["bok"] = "init"
    /\ \E msg \in msgs_recv["bok"]:
        /\ msg.from = "usr" /\ msg.to = "bok" /\ msg.op = "get"
            /\ msgs_recv' = [msgs_recv EXCEPT !["bok"] = @ \ {msg}]
            /\ pc' = [pc EXCEPT !["bok"] = "get_recv"]
    /\ UNCHANGED <<sys_state, msgs_usr, msgs_send, ink_state, bok_state, pen_state>>
Bok_ProcGet ==
    /\ sys_state # "done"
    /\ pc["bok"] = "get_recv"
    /\ pc' = [pc EXCEPT !["bok"] = "fetch_head"]
    /\ UNCHANGED <<msgs_recv, msgs_usr, msgs_send, ink_state, bok_state, pen_state, sys_state>>
Bok_FetchHead ==
    /\ sys_state # "done"
    /\ pc["bok"] = "fetch_head"
    /\ \E has_ledger_cache \in {TRUE, FALSE}:
            IF has_ledger_cache THEN
                pc' = [pc EXCEPT !["bok"] = "get_recv_head"]
            ELSE
                \* pc' = [pc EXCEPT !["bok"] = "get_send_fetch"]
                pc' = [pc EXCEPT !["bok"] = "get_send_fetch"]
    /\ UNCHANGED <<msgs_recv, msgs_usr, msgs_send, ink_state, bok_state, pen_state, sys_state>>

Bok_SendFetch ==
    /\ sys_state # "done"
    /\ pc["bok"] = "get_send_fetch"
    /\  LET
            msg == Message("bok", "pen", "get")
        IN
            /\ msgs_recv' = [msgs_recv EXCEPT !["pen"] = @ \cup {msg}]
            /\ msgs_send' = [msgs_send EXCEPT !["bok"] = Append(@, msg)]
            /\ pc' = [pc EXCEPT !["bok"] = "wait_fetch"]
    /\ UNCHANGED <<msgs_usr, ink_state, bok_state, pen_state, sys_state>>

Pen_RecvFetch ==
    /\ sys_state # "done"
    /\ pc["pen"] = "init"
    /\ \E msg \in msgs_recv["pen"]:
        /\ msg.from = "bok" /\ msg.to = "pen" /\ msg.op = "get"
            /\ msgs_recv' = [msgs_recv EXCEPT !["pen"] = @ \ {msg}]
            /\ pc' = [pc EXCEPT !["pen"] = "get_pen_fetch_head"]
    /\ UNCHANGED <<msgs_usr, msgs_send, ink_state, bok_state, pen_state, sys_state>>
Pen_SendFetch ==
    /\ sys_state # "done"
    /\ pc["pen"] = "send_fetch"
    /\  LET
            msg == Message("pen", "bok", "get")
        IN
            /\ msgs_recv' = [msgs_recv EXCEPT !["bok"] = @ \cup {msg}]
            /\ msgs_send' = [msgs_send EXCEPT !["pen"] = Append(@, msg)]
            /\ pc' = [pc EXCEPT !["pen"] = "init"]
    /\ UNCHANGED <<msgs_usr, ink_state, bok_state, pen_state, sys_state>>
Pen_TryFetchHeadCache ==
    /\ sys_state # "done"
    /\ pc["pen"] = "get_pen_fetch_head"
    /\ \E head_found_in_l0_cache \in {TRUE, FALSE}:
            IF head_found_in_l0_cache THEN
                pc' = [pc EXCEPT !["pen"] = "send_fetch"]
            ELSE
                pc' = [pc EXCEPT !["pen"] = "get_search_tree"]
    /\ UNCHANGED <<msgs_recv ,msgs_usr, msgs_send, ink_state, bok_state, pen_state, sys_state>>
Pen_TreeSearchHead ==
    /\ sys_state # "done"
    /\ pc["pen"] = "get_search_tree"
    /\ \E head_found_in_tree \in {TRUE, FALSE}:
            IF head_found_in_tree THEN
                pc' = [pc EXCEPT !["pen"] = "send_fetch"]
            ELSE
                pc' = [pc EXCEPT !["pen"] = "send_fetch"]
    /\ UNCHANGED <<msgs_recv ,msgs_usr, msgs_send, ink_state, bok_state, pen_state, sys_state>>

Bok_RecvFetch ==
    /\ sys_state # "done"
    /\ pc["bok"] = "wait_fetch"
    /\ \E msg \in msgs_recv["bok"]:
            /\ msg.from = "pen" /\ msg.to = "bok" /\ msg.op = "get"
            /\ pc' = [pc EXCEPT !["bok"] = "get_recv_head"]
    /\ UNCHANGED <<msgs_recv, msgs_usr, msgs_send, ink_state, bok_state, pen_state, sys_state>>

Bok_RecvHead ==
    /\ sys_state # "done"
    /\ pc["bok"] = "get_recv_head"
    /\ \E head_not_found \in {TRUE, FALSE}:
        IF head_not_found THEN
            pc' = [pc EXCEPT !["bok"] = "get_no_head"]
        ELSE
            \E obj_is_tomb \in {TRUE, FALSE}:
                IF obj_is_tomb THEN
                    pc' = [pc EXCEPT !["bok"] = "get_obj_tomb"]
                ELSE
                    \E obj_is_exp \in {TRUE, FALSE}:
                        IF obj_is_exp THEN
                            pc' = [pc EXCEPT !["bok"] = "get_obj_exp"]
                        ELSE
                            pc' = [pc EXCEPT !["bok"] = "get_send_fetch_value"]
                            \* pc' = [pc EXCEPT !["bok"] = "get_fetch_obj"]
    /\ UNCHANGED <<msgs_recv, msgs_usr, msgs_send, ink_state, bok_state, pen_state, sys_state>>
Bok_HeadNotFound ==
    /\ sys_state # "done"
    /\ pc["bok"] = "get_no_head"
    /\ pc' = [pc EXCEPT !["bok"] = "get_not_found"]
    /\ UNCHANGED <<msgs_recv, msgs_usr, msgs_send, ink_state, bok_state, pen_state, sys_state>>
Bok_HeadObjIsTomb ==
    /\ sys_state # "done"
    /\ pc["bok"] = "get_obj_tomb"
    /\ pc' = [pc EXCEPT !["bok"] = "get_not_found"]
    /\ UNCHANGED <<msgs_recv, msgs_usr, msgs_send, ink_state, bok_state, pen_state, sys_state>>
Bok_HeadObjIsExpired ==
    /\ sys_state # "done"
    /\ pc["bok"] = "get_obj_exp"
    /\ pc' = [pc EXCEPT !["bok"] = "get_not_found"]
    /\ UNCHANGED <<msgs_recv, msgs_usr, msgs_send, ink_state, bok_state, pen_state, sys_state>>

Bok_GetSendUsr ==
    /\ sys_state # "done"
    /\
        \/ pc["bok"] = "get_not_found"
        \/ pc["bok"] = "get_found"
    /\
        LET msg == Message("bok", "usr", "get")
        IN
            /\ msgs_recv' = [msgs_recv EXCEPT !["usr"] = @ \cup {msg}]
            /\ msgs_send' = [msgs_send EXCEPT !["bok"] = Append(@, msg)]
            /\ pc' = [pc EXCEPT !["bok"] = "init"]
            /\ sys_state' = "done"
    /\ UNCHANGED <<msgs_usr, ink_state, bok_state, pen_state>>

Bok_SendFetchValueInk ==
    /\ sys_state # "done"
    /\ pc["bok"] = "get_send_fetch_value"
    /\
        LET msg == Message("bok", "ink", "get")
        IN
            /\ msgs_recv' = [msgs_recv EXCEPT !["ink"] = @ \cup {msg}]
            /\ msgs_send' = [msgs_send EXCEPT !["bok"] = Append(@, msg)]
            /\ pc' = [pc EXCEPT !["bok"] = "wait_value"]
    /\ UNCHANGED <<msgs_usr, ink_state, bok_state, pen_state, sys_state>>
Ink_RecvFetchValueBok ==
    /\ sys_state # "done"
    /\ pc["ink"] = "init"
    /\ \E msg \in msgs_recv["ink"]:
        /\ msg.from = "bok" /\ msg.to = "ink" /\ msg.op = "get"
        /\ msgs_recv' = [msgs_recv EXCEPT !["ink"] = @ \ {msg}]
        /\ pc' = [pc EXCEPT !["ink"] = "get_value"]
    /\ UNCHANGED <<msgs_usr, ink_state, bok_state, pen_state, msgs_send, sys_state>>
Ink_SendValueBok ==
    /\ sys_state # "done"
    /\ pc["ink"] = "get_send_value"
    /\
        LET msg == Message("ink", "bok", "get")
        IN
            /\ msgs_recv' = [msgs_recv EXCEPT !["bok"] = @ \cup {msg}]
            /\ msgs_send' = [msgs_send EXCEPT !["ink"] = Append(@, msg)]
            /\ pc' = [pc EXCEPT !["ink"] = "init"]
    /\ UNCHANGED <<msgs_usr, ink_state, bok_state, pen_state, sys_state>>
Ink_GetValueFromManifestIfExists ==
    /\ sys_state # "done"
    /\ pc["ink"] = "get_value"
    /\ \E value_exists_in_manifest \in {TRUE, FALSE}:
            IF value_exists_in_manifest THEN
                pc' = [pc EXCEPT !["ink"] = "get_send_value"]
            ELSE
                pc' = [pc EXCEPT !["ink"] = "get_send_value"]
    /\ UNCHANGED <<msgs_usr, msgs_send, msgs_recv, ink_state, bok_state, pen_state, sys_state>>
Bok_RecvValueInk ==
    /\ sys_state # "done"
    /\ pc["bok"] = "wait_value"
    /\ \E msg \in msgs_recv["bok"]:
        /\ msg.from = "ink" /\ msg.to = "bok" /\ msg.op = "get"
        /\ msgs_recv' = [msgs_recv EXCEPT !["bok"] = @ \ {msg}]
        /\ pc' = [pc EXCEPT !["bok"] = "get_found"]
    /\ UNCHANGED <<msgs_usr, msgs_send, ink_state, bok_state, pen_state, sys_state>>

Ink_GetValueFromJournal ==
    \/ Bok_SendFetchValueInk
    \/ Ink_RecvFetchValueBok
    \/ Ink_GetValueFromManifestIfExists
    \/ Ink_SendValueBok
    \/ Bok_RecvValueInk
Ink_PutValueToJournal ==
    \/ Ink_RecvWriteReqBok
    \/ Ink_CheckCanWrite
    \/ Ink_RollActiveJournal
    \/ Ink_WriteValueToJournal
    \/ Ink_SendChangesToBok
Pen_Pushmem ==
    \/ Pen_RecvPushmemBok
    \/ Pen_ProcPushmemBok
    \/ Pen_RollMemory
    \/ Pen_RetryPushLaterBok
    \/ Pen_Push
    \/ Pen_SendPushmemBok
Pen_FetchHead ==
    \/ Bok_SendFetch
    \/ Bok_RecvFetch
    \/ Pen_TryFetchHeadCache
    \/ Pen_TreeSearchHead
    \/ Pen_SendFetch
    \/ Pen_RecvFetch
Leveled_Get ==
    \/ Usr_SendGet
    \/ Bok_RecvGetUsr
    \/ Bok_ProcGet
    \/ Bok_FetchHead
    \/ Bok_RecvHead
    \/ Bok_HeadObjIsExpired
    \/ Bok_HeadObjIsTomb
    \/ Bok_HeadNotFound
    \/ Ink_GetValueFromJournal
    \/ Pen_FetchHead
    \/ Bok_GetSendUsr
Leveled_Put ==
    \/ Usr_SendPut
    \/ Bok_RecvPutUsr
    \/ Bok_SendWriteToJournal
    \/ Ink_PutValueToJournal
    \/ Bok_RecvJournalChanges
    \/ Bok_AddToLedgerCache
    \/ Bok_CheckPushMemReady
    \/ Bok_SendPushMemPen
    \/ Pen_Pushmem
    \/ Bok_RecvPushMemOk
    \/ Bok_CleanCache
    \/ Bok_PutSendUsr

Terminated ==
    /\ sys_state = "done"
    /\ msgs_usr = <<>>
    /\ UNCHANGED vars

Next ==
    \/ Leveled_Get
    \/ Leveled_Put
    \/ Terminated

====