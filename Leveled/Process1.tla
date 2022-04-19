---- MODULE Process1 ----

CONSTANTS
    \* identification of the process
    id,
    state

ProcS_Idle == "ProcS_Idle"
ProcS_Busy == "ProcS_Busy"
ProcS_Unavailable == "ProcS_Unavailable"
ProcS_Status == {ProcS_Idle, ProcS_Busy, ProcS_Unavailable}

VARIABLE status

vars == <<status>>

BecomeIdle ==
    /\ status = ProcS_Busy

    /\ status' = ProcS_Idle

BecomeBusy ==
    /\ status = ProcS_Idle

    /\ status' = ProcS_Busy

BecomeUnreachablle ==
    /\ status' = ProcS_Unavailable

Recover ==
    /\ status = ProcS_Unavailable

    /\ status' = ProcS_Idle

TypeInv ==
    /\ status \in ProcS_Status

Init == 
    /\ status = ProcS_Idle

Next ==
    \/ BecomeIdle
    \/ BecomeBusy
    \/ BecomeUnreachablle
    \/ Recover
====