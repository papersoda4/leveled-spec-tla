---- MODULE Leveled ----
EXTENDS TLC

VARIABLE 
    sys_name

Init == 
    sys_name = "leveled"

Next == 
    sys_name' = "leveled"

SysNameInv ==
    sys_name = "leveled"
====