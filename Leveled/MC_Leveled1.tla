---- MODULE MC_Leveled1 ----
EXTENDS Leveled1
CONSTANTS
    proc_count
Init1 == /\ Init
LOCAL CommunicatingProcessCountEquals(expected) == 
    /\  LET actual == Cardinality(Processes)
        IN actual = expected
LOCAL IsOperationAvailable(op) == /\ op \in Operations
LOCAL IsActorDefined(actor) == /\ actor \in Processes
LOCAL IsProcQueueEmpty(proc) == msg_qs[proc] = <<>>
LOCAL EmptyState == /\ UNCHANGED <<msg_qs>>
AllProccessQueuesInitiallyEmptyInv == /\ \A p \in Processes: IsProcQueueEmpty(p)
CommunicatingProcCountInv == /\ CommunicatingProcessCountEquals(proc_count)
PutOperationIsAvailableInv == /\ IsOperationAvailable(OpType_Put)
BokActorDefinedInv == /\ IsActorDefined(ProcType_Bok)
InkActorDefinedInv == /\ IsActorDefined(ProcType_Ink)
PenActorDefinedInv == /\ IsActorDefined(ProcType_Pen)
Next1 == \/ EmptyState
Spec1 == Init1 /\ [][Next1]_vars
====
