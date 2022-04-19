---- MODULE MC_Process1 ----
EXTENDS Process1

(* Specification *)
Fairness == WF_status(BecomeUnreachablle)
Spec == Init /\ [][Next]_vars /\ Fairness

(* Properties *)
Failure == status = ProcS_Unavailable
Success == ~Failure
\* process can fail at any time
CanFail == []<>Failure
\* process can recover from failure
CanRecoverFromFail == Failure => <>Success
\* it's possible for process to not recover from failure
CanFailHard == Failure => []Failure
====