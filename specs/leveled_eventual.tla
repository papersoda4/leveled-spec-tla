---- MODULE leveled_eventual ----
EXTENDS TLC, FiniteSets, Naturals, Sequences
(***************************************************************************)
(* State                                                                   *)
(***************************************************************************)
VARIABLES
    pc,      \* state of the system
    journal, \* sequential structure in Leveled for storing contents of objects
    sqn,     \* reference to the newest added object in Journal (object metadata)
    ledger,  \* structure in Leveled for storing metadata for objects
    ledger_update_status, \* status of ledger from perspective of updating ledger to newest state
    get_obj_val, \* objects' contents , received by key in get operation
    write_ack    \* boolean flag, indicating that write had been acknowledged
(***************************************************************************)
(* Structures                                                              *)
(***************************************************************************)
vars == <<journal, ledger, pc, ledger_update_status, get_obj_val, write_ack, sqn>>
(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)
UpdateLedger ==
    /\ write_ack = TRUE /\ ledger_update_status = "updating"
    /\ LET object_location == sqn IN
        /\ ledger' = [ledger EXCEPT !["key"] = object_location]
        /\ ledger_update_status' = "updated"
    /\ UNCHANGED <<pc, journal, get_obj_val, write_ack, sqn>>

GetObj ==
    /\ write_ack = TRUE
    /\
        \/ ledger_update_status = "before_update"
        \/ ledger_update_status = "updating"
        \/ ledger_update_status = "updated"

    /\ get_obj_val' = journal[ledger["key"]]["key"]
    /\ pc' = "done"
    /\ UNCHANGED <<journal, ledger, ledger_update_status, write_ack, sqn>>

PutObj ==
    /\ ~write_ack

    /\ sqn' = Len(journal) + 1
    /\ journal' = Append(journal, [key |-> "obj_new"])
    /\ write_ack' = TRUE
    /\ ledger_update_status' = "updating"
    /\ UNCHANGED <<pc, ledger, get_obj_val>>

Terminate ==
    /\ pc = "done"
    /\ UNCHANGED vars
(***************************************************************************)
(* Configuration                                                           *)
(***************************************************************************)
Init ==
    /\ pc = "active"
    /\ journal = <<[key |-> "obj_old"]>>
    /\ ledger = [key |-> 1]
    /\ ledger_update_status = "before_update"
    /\ get_obj_val = "none"
    /\ write_ack = FALSE
    /\ sqn = Len(journal)

Next ==
    \/ UpdateLedger
    \/ PutObj
    \/ GetObj
    \/ Terminate
(***************************************************************************)
(* Verification                                                            *)
(***************************************************************************)
TypeInv ==
    /\ pc \in {"active", "done"}
    /\ ledger_update_status \in {"before_update", "updating", "updated"}
    /\ get_obj_val \in {"none", "obj_old", "obj_new"}
    /\ write_ack \in BOOLEAN
    /\ sqn \in Nat \ {0}

GetMayReturnOldValAfterWriteAckOfNewVal ==
    <>(write_ack = TRUE /\ get_obj_val = "obj_old")

GetWillReturnNewestObjAfterObjMetadataUpdated ==
    ledger_update_status = "updated" ~> get_obj_val = "obj_new"

EventualConsistency ==
    /\ GetMayReturnOldValAfterWriteAckOfNewVal
    /\ GetWillReturnNewestObjAfterObjMetadataUpdated

Fairness ==
    /\ EventualConsistency
    /\ WF_vars(Terminate)

Spec == Init /\ [][Next]_vars /\ Fairness
====