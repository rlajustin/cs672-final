--------------------------- MODULE ThreePhaseCommit ---------------------------
(* Based on the TLA+ video course + in-class notes for three phase commit *)
CONSTANT SERVERS

VARIABLES
    coordState,
    servState,
    servReady,     (* in eyes of coordinator *)
    servPrecommit, (* in eyes of coordinator *)
    msgs
    
Messages == [type: {"ready", "precommit", "commit"}, server: SERVERS]
            \cup [type: {"Ready", "Precommit", "Commit", "Abort"}]

TypeOK ==
    /\ servState \in [SERVERS -> {"idle", "ready", "precommitted", "committed", "aborted"}]
    /\ coordState \in {"init", "waitingR", "waitingP", "done"}
    /\ servReady \subseteq SERVERS
    /\ msgs \subseteq Messages

Init ==
    /\ servState = [s \in SERVERS |-> "idle"]
    /\ coordState = "init"
    /\ servReady = {}
    /\ servPrecommit = {}
    /\ msgs = {}

----------------------------------------------------------
(* Define all of the actions that can be performed *)

(* COORDINATOR ACTIONS *)
(* Coordinator asks for ready responses *)
CoordReady ==
    /\ coordState = "init"
    /\ coordState' = "waitingR"
    /\ servReady = {}
    /\ servPrecommit = {}
    /\ msgs' = msgs \cup {[type |-> "Ready"]}
    /\ UNCHANGED <<servState, servReady, servPrecommit>>

(* Coordinator receives ready message from server *)
CoordRecReady(s) ==
    /\ coordState = "waitingR"
    /\ [type |-> "ready", server |-> s] \in msgs
    /\ servReady' = servReady \cup {s}
    /\ UNCHANGED <<coordState, servState, servPrecommit, msgs>>

(* Coordinator broadcasts precommit message *)
CoordPrecommit ==
    /\ coordState = "waitingR"
    /\ coordState' = "waitingP"
    /\ servReady = SERVERS
    /\ servPrecommit = {}
    /\ msgs' = msgs \cup {[type |-> "Precommit"]}
    /\ UNCHANGED <<servState, servReady, servPrecommit>>

(* Coordinator receives precommit message from server *)
CoordRecPrecommit(s) ==
    /\ coordState = "waitingP"
    /\ [type |-> "precommit", server |-> s] \in msgs
    /\ servPrecommit' = servPrecommit \cup {s}
    /\ UNCHANGED <<coordState, servState, servReady, msgs>>

(* Coordinator broadcasts commit message *)
CoordCommit ==
    /\ coordState = "waitingP"
    /\ coordState' = "done"
    /\ servPrecommit = SERVERS
    /\ msgs' = msgs \cup {[type |-> "Commit"]}
    /\ UNCHANGED <<servState, servReady, servPrecommit>>

(* Coordinator broadcasts abort message *)
CoordAbort ==
    /\ coordState \in {"init", "waitingR", "waitingP"}
    /\ coordState' = "done"
    /\ msgs' = msgs \cup {[type |-> "Abort"]}
    /\ UNCHANGED <<servState, servReady, servPrecommit>>

(* SERVER ACTIONS *)
(* Server receives + sends ready message *)
ServReady(s) ==
    /\ servState[s] = "idle"
    /\ servState' = [servState EXCEPT ![s] = "ready"]
    /\ [type |-> "Ready"] \in msgs
    /\ msgs' = msgs \cup {[type |-> "ready", server |-> s]}
    /\ UNCHANGED <<coordState, servReady, servPrecommit>>

(* Server receives + sends precommit message *)
ServPrecommit(s) ==
    /\ servState[s] = "ready"
    /\ servState' = [servState EXCEPT ![s] = "precommitted"]
    /\ [type |-> "Precommit"] \in msgs
    /\ msgs' = msgs \cup {[type |-> "precommit", server |-> s]}
    /\ UNCHANGED <<coordState, servReady, servPrecommit>>
(* Maybe separate these two ^^ *)

(* Server receives commit message, commits *)
ServRecCommit(s) ==
    /\ servState[s] = "precommitted"
    /\ [type |-> "Commit"] \in msgs
    /\ servState' = [servState EXCEPT ![s] = "committed"]
    /\ UNCHANGED <<coordState, servReady, servPrecommit, msgs>>

(* Server receives abort message, aborts *)
ServRecAbort(s) ==
    /\ [type |-> "Abort"] \in msgs
    /\ servState' = [servState EXCEPT ![s] = "aborted"]
    /\ UNCHANGED <<coordState, servReady, servPrecommit, msgs>>

(* MAKE SURE HANDLE CRASH AFTER PRECOMMITTED *)
(* Test with and without this *)
\*ServCrash(s) == (* for whatever reason server aborts/crashes *)
\*    /\ servState[s] \in {"idle", "ready", "precommitted", "committed"}
\*    /\ servState' = [servState EXCEPT ![s] = "aborted"]
\*    /\ UNCHANGED <<coordState, servReady, servPrecommit, msgs>>

Next ==
    \/ CoordReady \/ CoordPrecommit \/ CoordCommit \/ CoordAbort
    \/ \E s \in SERVERS :
        \/ CoordRecReady(s) \/ CoordRecPrecommit(s)
        \/ ServReady(s) \/ ServPrecommit(s) \/ ServRecCommit(s) \/ ServRecAbort(s) \* \/ ServCrash(s)

-------------------------------------------------------------
Consistent ==
    \A s1, s2 \in SERVERS : ~ /\ servState[s1] = "committed"
                              /\ servState[s2] = "aborted"
-------------------------------------------------------------
Spec == Init /\ [][Next]_<<coordState, servState, servReady, servPrecommit, msgs>>

THEOREM Spec => [](TypeOK /\ Consistent)

=============================================================================