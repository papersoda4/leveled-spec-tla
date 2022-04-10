---- MODULE MC_Leveled2 ----
EXTENDS Leveled2

Init2 ==
    /\ Init
    /\ usr_msgs = <<PutMessage("Key", "Value")>> 

Spec == Init2 /\ [][Next]_vars /\ WF_pc(Next)
Termination == <>(pc = PC_Done)

====