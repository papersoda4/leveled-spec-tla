---- MODULE Leveled3 ----

EXTENDS FiniteSets, Sequences, Naturals

VARIABLES
    \* set of all sent messages
    msgs,
    \* state of the system
    ss,
    \* map of states for each process
    ps,
    \* sequential number of journal
    jsqn

vars == <<msgs, ss, ps, jsqn>>

User == "User"
Actor_Pen == "Penciler"
Actor_Ink == "Inker"
Actor_Bok == "Bookie"
Actors == {Actor_Pen, Actor_Bok, Actor_Ink}

Entity_Jor == "Journal"
Entity_Led == "Lederger"
Entity_LedCache == "LedgerCache"
Entities == {Entity_Jor, Entity_Led, Entity_LedCache}

PS_Idle == "ProccessState_Idle"
PS_Busy == "ProccessState_Busy"
PS_Unavailable == "ProccessState_Unavailable"
ProcessStates == {PS_Idle, PS_Busy, PS_Unavailable}

JouFull == "JournalFull"
JouNotFull == "JournalNotFull"
JournalStates == {JouFull, JouNotFull}

PC_Started == "Started"
PC_Done == "Done"
SystemStates == {PC_Started, PC_Done}

OpType_Put == "Put"
OpType_PushMem == "PushMem"
Operations == {OpType_Put, OpType_PushMem}

Cmd_PersistJo == "PersistJor"
Cmd_PersistCa == "PersistCache"

Resp_Ok == "Ok"
Resp_Wait == "Wait"
Resp_Reject == "Reject"

Message(from, to, op_type) == [from |-> from, to |-> to, op |-> op_type]

Messages == 
         Message(User, Actor_Bok, OpType_Put)
    \cup Message(Actor_Bok, Actor_Ink, OpType_Put) 
    \cup Message(Actor_Bok, Entity_Jor, Cmd_PersistJo)
    \cup Message(Entity_Jor, Actor_Bok, Resp_Ok)
    \cup Message(Entity_Jor, Actor_Bok, Resp_Wait)

SendMsg(msg) == msgs' = msgs \cup {msg}
RecvMsg(msg) == msg \in msgs /\ msgs' = msgs \ {msg}

Terminate == ss' = PC_Done
SetProcessState(pid, state) == ps' = [ps EXCEPT ![pid] = state]
IsProcessInState(pid, state) == /\ ps[pid] = state
HasMessage(from, to, type) == 
    /\ \E msg \in msgs:
        /\ msg.from = from /\ msg.to = to /\ msg.op = type

Usr_SendPut ==
    /\ SendMsg(Message(User, Actor_Bok, OpType_Put))
    /\ UNCHANGED <<ss, ps, jsqn>>

Bok_RecvPutUsr ==    
    /\ IsProcessInState(Actor_Bok, PS_Idle) 
    /\ HasMessage(User, Actor_Bok, OpType_Put)

    /\ SendMsg(Message(Actor_Bok, Actor_Ink, OpType_Put))
    /\ UNCHANGED <<ss, ps, jsqn>> 

Ink_RecvPutBok ==
    /\ IsProcessInState(Actor_Ink, PS_Idle) 
    /\ HasMessage(Actor_Bok, Actor_Ink, OpType_Put)

    \* /\ jsqn' = jsqn + 1
    /\ Terminate
    /\ UNCHANGED  <<msgs, ps, jsqn>>

\* Ink_RollJournal ==

Terminated ==
    /\ ss = PC_Done
    
    /\ UNCHANGED vars

BecomeIdle(pid) == 
    ps[pid] = PS_Busy /\ SetProcessState(pid, PS_Idle) /\ UNCHANGED <<msgs, ss, jsqn>>

BecomeBusy(pid) == 
    ps[pid] = PS_Idle /\ SetProcessState(pid, PS_Busy) /\ UNCHANGED <<msgs, ss, jsqn>>

BecomeUnreachablle(pid) == 
    SetProcessState(pid, PS_Unavailable) /\ UNCHANGED <<msgs, ss, jsqn>>

Recover(pid) == 
    ps[pid] = PS_Unavailable /\ SetProcessState(pid, PS_Idle) /\ UNCHANGED <<msgs, ss, jsqn>>

ProcessNext ==
    \E p \in Actors:
        \/ BecomeIdle(p)
        \/ BecomeBusy(p)
        \/ BecomeUnreachablle(p)
        \/ Recover(p)

ActorNext ==
    \/ Usr_SendPut
    \/ Bok_RecvPutUsr
    \/ Ink_RecvPutBok

Next == 
    \/ ActorNext
    \/ ProcessNext
    \/ Terminated

Fairness ==
    /\ WF_ss(Terminated) 
    /\ \E p \in Actors:
        WF_ps(BecomeUnreachablle(p))

TypeInv ==
    /\ ss \in SystemStates
    /\ ps \in [Actors -> ProcessStates]
    /\ msgs \subseteq Messages 
    \* /\ jsqn \in Nat

Init ==
    /\ ss = PC_Started
    /\ msgs = {}
    /\ ps = [a \in Actors |-> PS_Idle]
    /\ jsqn = 0

JSqnConstraint == jsqn < 10
====