---- MODULE MC_Leveled ----
\* EXTENDS Leveled

\* Fairness ==
\*     /\ WF_<<sys_state, msgs_usr>>(Terminated)

\* ValidTermination == TRUE
\*     \* <>(sys_state = "done" /\
\*     \*     \A actor \in {"ink", "bok", "pen"}:
\*     \*         Cardinality(msgs_recv[actor]) = 0)

\* Spec == Init /\ [][Next]_vars /\ Fairness
====