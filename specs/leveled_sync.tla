---- MODULE leveled_sync ----
EXTENDS TLC, Naturals, FiniteSets, Sequences
(***************************************************************************)
(* Converts a sequence to a set                                            *)
(* Range(<<"a", "b", "b">>) = {"a", "b"}                                   *)
(***************************************************************************)
Range(seq) == {seq[x] : x \in DOMAIN seq}
(***************************************************************************)
(* State                                                                   *)
(***************************************************************************)
VARIABLES
    system_state, \* current status of the execution of the system
    (*
        map of Leveled actors to their current statuses
        actor_state["bok"] = "init"
        actor_state["ink"] = "send_msg"
    *)
    actor_state
(***************************************************************************)
(* Messages                                                                *)
(***************************************************************************)
VARIABLES
    msgs_sent, \* messages sent by actor processes
    msgs_recv, \* messages received by actor processes
    usr_req    \* messages that the user sends to the bookie
(***************************************************************************)
(* Structures                                                              *)
(***************************************************************************)
vars == <<system_state, actor_state, msgs_sent, msgs_recv, usr_req>>
Nil == "nil"
AnyVal == CHOOSE v \in {"any_val"}: v \notin {Nil}
Message(from, to, op, payload) == [from |-> from, to |-> to, op |-> op, payload |-> payload]
(***************************************************************************)
(* Domain                                                                  *)
(***************************************************************************)
USER_STATES == {"init", "sent_get", "sent_put"}
SYSTEM_STATES == {"active", "done"}
SYSTEM_ACTORS == {"bok", "ink", "pen"} \cup {"usr"}
BOOKIE_STATES == {"init", "recv_get_usr" ,"done"}
INKER_STATES == {"init"}
PENCILLER_STATES == {"init"}
OPERATION_TYPES == {"get", "put"}
MESSAGES == {
    Message("usr", "bok", "get", Nil),
    Message("bok", "usr", "get", AnyVal)
}
(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)
Usr_SendGet ==
    /\ system_state = "active"
    /\ usr_req # <<>>
    /\ LET msg == Head(usr_req) IN
        /\ msg.op = "get"

        /\ msgs_recv' = [msgs_recv EXCEPT !["bok"] = @ \cup {msg}]
        /\ msgs_sent' = [msgs_sent EXCEPT !["usr"] = @ \cup {msg}]
        /\ usr_req' = Tail(usr_req)
    /\ UNCHANGED <<system_state, actor_state>>

Bok_RecvGet ==
    /\ system_state = "active"
    /\ actor_state["bok"] = "init"
    /\ \E msg \in msgs_recv["bok"]:
        /\ msg.from = "usr" /\ msg.to = "bok" /\ msg.op = "get"
        /\ msgs_recv' = [msgs_recv EXCEPT !["bok"] = @ \ {msg}]

        /\ actor_state' = [actor_state EXCEPT !["bok"] = "recv_get_usr"]
        /\ msgs_sent' = [msgs_sent EXCEPT !["bok"] = @ \cup {Message("bok", "usr", "get", AnyVal)}]
        /\ system_state' = "done"
        /\ UNCHANGED <<usr_req>>

Termination ==
    /\ system_state = "done"
    /\ UNCHANGED vars
(***************************************************************************)
(* Configuration                                                           *)
(***************************************************************************)
Init ==
    \* control state
    /\ system_state = "active"
    /\ actor_state = [actor \in SYSTEM_ACTORS |-> "init"]
    \* messages
    /\ usr_req = <<Message("usr", "bok", "get", Nil)>>
    /\ msgs_sent = [actor \in SYSTEM_ACTORS |-> {}]
    /\ msgs_recv = [u \in {"usr"} |-> Range(usr_req)] @@ [actor \in SYSTEM_ACTORS |-> {}]

Next ==
    \/ Usr_SendGet
    \/ Bok_RecvGet
    \/ Termination
(***************************************************************************)
(* Verification                                                            *)
(***************************************************************************)
TypeInv ==
    /\ system_state \in SYSTEM_STATES

    /\ actor_state["bok"] \in BOOKIE_STATES
    /\ actor_state["ink"] \in INKER_STATES
    /\ actor_state["pen"] \in PENCILLER_STATES

    /\ msgs_sent \in [SYSTEM_ACTORS -> SUBSET MESSAGES]
    /\ msgs_recv \in [SYSTEM_ACTORS -> SUBSET MESSAGES]

Responsive == []<>(\A actor \in SYSTEM_ACTORS: Cardinality(msgs_recv[actor]) = 0)

Synchronous == []<>(
    \A a1, a2 \in SYSTEM_ACTORS:
        \E m1 \in msgs_sent[a1]:
            \E m2 \in msgs_sent[a2]:
                m1.from = m2.to /\ m1.to = m2.from /\ m1.op = m2.op)

Fairness ==
    /\ Responsive
    /\ Synchronous
    /\ WF_<<system_state>>(Termination)

Spec == Init /\ [][Next]_vars /\ Fairness
====