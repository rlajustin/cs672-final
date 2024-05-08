-------------------------------- MODULE SyncHotStuff --------------------------------

EXTENDS Integers, FiniteSets

CONSTANT
    N,T,
    Byzantine,Honest,
    MaxView,
    LeaderFunc (* maps views to leaders *)
    
Views == 0..MaxView \* view 0 is nil
Nodes == 0..N \* node 0 is nil

TimeType == [Nodes -> Int]
BlockType == [Views -> Int]
QCType == [replica: Nodes, sigs : {S \in SUBSET Nodes : Cardinality(S) > T}, block: BlockType] \* add invariant to not allow messages without QC
NilQC == {[replica |-> r, sigs |-> Nodes, block |-> [v \in Views |->  0]] : r \in Nodes} \* give everyone a NilQC

PrepQuorumType == [replica: Nodes, sigs: SUBSET Nodes, block: BlockType]

VARIABLES
    curView,        \* a process round number: Honest -> Views
    phase,          \* a process phase: Honest -> { "PREPARE", "PRECOMMIT", "COMMIT"}
    sluggish,       \* set of sluggish replicas Honest -> {0,1}
    time,           \* Nodes -> Int;
    msgsPropose,
    msgsVote,
    msgsCommit,
    prepQuorum,     \* every replica has
    QCs             \* maps from nodes to quorum certificates (unforgeable)

variables == <<curView, phase, sluggish, time, msgsPropose, msgsVote, msgsCommit, QCs>>

ASSUME
    /\ N = Cardinality(Honest \cup Byzantine)
    /\ N > 2*T

(*  /\ N > 2*(Cardinality(Byzantine \cup Sluggish))    MOVE THIS TO INVARIANT CHECKER THING *)

Phases == {"WAIT", "PRECOMMIT", "COMMIT", "EQUIVOCATE"}

------------------------------------

TypeOK ==
    /\ curView \in [Honest -> Views]
    /\ phase \in [Honest -> Phases]
    /\ sluggish \subseteq Honest
    /\ time \in [Nodes -> Int]
    /\ msgsPropose \subseteq   [sender:     Nodes,
                                recipient:  Nodes,
                                view:       Views,
                                time:       TimeType,
                                block:      BlockType,
                                qc:         QCs]
                                
    /\ msgsVote \subseteq      [sender:     Nodes,
                                recipient:  Nodes,
                                view:       Views,
                                time:       TimeType,
                                block:      BlockType]
                                
    /\ msgsCommit \subseteq    [sender:     Nodes,
                                recipient:  Nodes,
                                view:       Views,
                                time:       TimeType,
                                block:      BlockType]
    /\ QCs \subseteq QCType
    
FaultyNodes ==
    /\ N > 2*(Cardinality(Byzantine \cup sluggish))

Init ==
    /\ curView = [r \in Honest |-> 1]
    /\ phase = [r \in Honest |-> "WAIT"]
    /\ sluggish = {}
    /\ time = [r \in Nodes |-> 0]
    /\ msgsPropose = {}
    /\ msgsVote = {}
    /\ msgsCommit = {}
    /\ QCs = NilQC

------------------------------------

(* LEADER ACTIONS *)
LeaderPropose(r) ==
    /\ phase[r] = "WAIT"
    /\ r = LeaderFunc[curView[r]]
    /\ \E quorum \in SUBSET (Nodes \ {0}), b \in BlockType:
        /\ [replica |-> r, sigs |-> quorum, block |-> [b EXCEPT ![curView[r]]=0]] \in QCs \* qc is from view curView[r]-1
        /\ Cardinality(quorum) > N \div 2
        /\ b[curView[r]] # 0 \* default 0 means view not empty
        \* maybe need to check view in the qc is consistent? or put that in an invariant
        /\ msgsPropose' = msgsPropose \cup {[sender |-> r, recipient |-> s, time |-> time[r], view |-> curView[r], block |-> b] : s \in Nodes}
    /\ phase' = [phase EXCEPT ![r] = "PRECOMMIT"] \* maybe remove???
    /\ UNCHANGED <<curView, sluggish, time, msgsVote, msgsCommit, QCs>>


(* REPLICA ACTIONS *)
RecievePropose(r) ==
    /\ phase[r] = "WAIT"
    /\ \E msg \in msgsPropose :
        /\ msg.time \leq time[r]-1
        /\ msg.recipient = r
        /\ ~ \E other \in msgsPropose :
            /\ other.block[other.view-1] # 0
            /\ other.block[other.view] = 1
            /\ other.view <= msg.view
        /\ msg.view-1 > curView[r] =>
            /\ QCs' = QCs \cup {[msg.qc EXCEPT !.replica = r]}
        /\ curView' = IF msg.view > curView[r] THEN [curView EXCEPT ![r] = msg.view] ELSE curView 
        /\ msgsPropose' = msgsPropose \cup {[sender |-> r, recipient |-> s, time |-> msg.time, view |-> msg.view, block |-> msg.block] : s \in Nodes}

PreCommit(r) ==
    /\ phase[r] = "WAIT"
    /\ phase' = [phase EXCEPT ![r] = "PRECOMMIT"]
    \* unfinished


=============================================================================
\* Modification History
\* Last modified Wed Apr 24 21:31:03 EDT 2024 by justinkim
\* Created Sat Apr 06 17:27:36 EDT 2024 by justinkim