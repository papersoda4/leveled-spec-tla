---- MODULE MC_Leveled1 ----
EXTENDS Leveled
CONSTANTS
    proc_count
Init1 == /\ Init
LOCAL CommunicatingProcessCountEquals(expected_proc_count) == 
    /\  LET actual_proc_count == Cardinality(Processes)
        IN actual_proc_count = expected_proc_count
LOCAL IsOperationAvailable(op) == /\ op \in Operations
LOCAL IsActorDefined(actor) == /\ actor \in Processes
LOCAL EmptyState == /\ UNCHANGED <<msg_qs>>
AllProccessQueuesInitiallyEmptyInv ==
    /\  \A proc \in Processes:
            msg_qs[proc] = <<>>
CommunicatingProcCountInv == /\ CommunicatingProcessCountEquals(proc_count)
PutOperationIsAvailableInv == /\ IsOperationAvailable(OpType_Put)
BokActorDefinedInv == /\ IsActorDefined(ProcType_Bok)
InkActorDefinedInv == /\ IsActorDefined(ProcType_Ink)
PenActorDefinedInv == /\ IsActorDefined(ProcType_Pen)
Next1 == \/ EmptyState
Spec1 == Init1 /\ [][Next1]_vars
====
