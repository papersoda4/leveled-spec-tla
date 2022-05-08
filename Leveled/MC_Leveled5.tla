---- MODULE MC_Leveled5 ----
EXTENDS Leveled5

Fairness ==
    /\ WF_sys_state(Terminated)

ValidTermination == TRUE
    \* <>(sys_state = "done" /\
    \*     \A actor \in {"ink", "bok", "pen"}:
    \*         Cardinality(msgs_recv[actor]) = 0)

Spec == Init /\ [][Next]_vars /\ Fairness
====