---- MODULE Leveled ----
EXTENDS TLC, FiniteSets, Sequences
ProcType_Pen == "Pen"
ProcType_Ink == "Ink"
ProcType_Bok == "Bok"
Processes == {ProcType_Pen, ProcType_Ink, ProcType_Bok}
OpType_Put == "PUT"
Operations == {OpType_Put}
VARIABLES msg_qs
vars == <<msg_qs>>
Init == /\ msg_qs = [p \in Processes |-> <<>>]
Next == /\ UNCHANGED msg_qs
Spec == Init /\ [][Next]_vars
====