---- MODULE MC_Leveled4 ----
EXTENDS Leveled4

Fairness ==
    /\ WF_sys_state(Terminated)

ValidTermination == TRUE
    \* <>(sys_state = "done" /\ 
    \*     \A actor \in {"ink", "bok", "pen"}:
    \*         Cardinality(msgs_recv[actor]) = 0)

Spec == Init /\ [][Next]_vars /\ Fairness
====