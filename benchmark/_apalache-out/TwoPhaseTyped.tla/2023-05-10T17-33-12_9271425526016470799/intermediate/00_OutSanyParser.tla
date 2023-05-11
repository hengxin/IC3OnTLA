--------------------------- MODULE 00_OutSanyParser ---------------------------

EXTENDS Integers, Sequences, FiniteSets, TLC, Apalache

CONSTANT
  (*
    @type: Set(RM);
  *)
  RM

VARIABLE
  (*
    The set of RMs from which the TM has received $"Prepared"$
 messages.
    @type: Set([type: Str, rm: RM]);
  *)
  msgs

VARIABLE
  (*
    @type: RM -> Str;
  *)
  rmState

VARIABLE
  (*
    $rmState[rm]$ is the state of resource manager RM.
    @type: Str;
  *)
  tmState

VARIABLE
  (*
    The state of the transaction manager.
    @type: Set(RM);
  *)
  tmPrepared

(*
  @type: Set([type: Str, rm: RM]);
*)
Message ==
  { [type |-> t, rm |-> r]: t \in {"Prepared"}, r \in RM }
    \union { [type |-> t]: t \in { "Commit", "Abort" } }

InitializeRM == RM = { "r1_OF_RM", "r2_OF_RM" }

Init ==
  rmState = [ rm \in RM |-> "working" ]
    /\ tmState = "init"
    /\ tmPrepared = {}
    /\ msgs = {}

(*
  *************************************************************************
 We now define the actions that may be performed by the processes, first 
 the TM's actions, then the RMs' actions.                                
*************************************************************************
  @type: (RM) => Bool;
*)
TMRcvPrepared(rm) ==
  tmState = "init"
    /\ [type |-> "Prepared", rm |-> rm] \in msgs
    /\ tmPrepared' = tmPrepared \union {rm}
    /\ UNCHANGED (<<rmState, tmState, msgs>>)

TMCommit ==
  tmState = "init"
    /\ tmPrepared = RM
    /\ tmState' = "committed"
    /\ msgs' = msgs \union {[type |-> "Commit"]}
    /\ UNCHANGED (<<rmState, tmPrepared>>)

TMAbort ==
  tmState = "init"
    /\ tmState' = "aborted"
    /\ msgs' = msgs \union {[type |-> "Abort"]}
    /\ UNCHANGED (<<rmState, tmPrepared>>)

(*
  @type: (RM) => Bool;
*)
RMPrepare(rm) ==
  rmState[rm] = "working"
    /\ rmState' = [ rmState EXCEPT ![rm] = "prepared" ]
    /\ msgs' = msgs \union {[type |-> "Prepared", rm |-> rm]}
    /\ UNCHANGED (<<tmState, tmPrepared>>)

(*
  @type: (RM) => Bool;
*)
RMChooseToAbort(rm) ==
  rmState[rm] = "working"
    /\ rmState' = [ rmState EXCEPT ![rm] = "aborted" ]
    /\ UNCHANGED (<<tmState, tmPrepared, msgs>>)

(*
  @type: (RM) => Bool;
*)
RMRcvCommitMsg(rm) ==
  [type |-> "Commit"] \in msgs
    /\ rmState' = [ rmState EXCEPT ![rm] = "committed" ]
    /\ UNCHANGED (<<tmState, tmPrepared, msgs>>)

(*
  @type: (RM) => Bool;
*)
RMRcvAbortMsg(rm) ==
  [type |-> "Abort"] \in msgs
    /\ rmState' = [ rmState EXCEPT ![rm] = "aborted" ]
    /\ UNCHANGED (<<tmState, tmPrepared, msgs>>)

(*
  ***********************************************************************
 The complete spec of the Two-Phase Commit protocol.                   
***********************************************************************
 copied from TCommit
*)
TCConsistent ==
  \A rm1 \in RM:
    \A rm2 \in RM: ~(rmState[rm1] = "aborted" /\ rmState[rm2] = "committed")

TPTypeOK ==
  rmState \in [RM -> { "working", "prepared", "committed", "aborted" }]
    /\ tmState \in { "init", "committed", "aborted" }
    /\ tmPrepared \in SUBSET RM
    /\ msgs \in SUBSET Message

Next ==
  (TMCommit \/ TMAbort)
    \/ (\E rm \in RM:
      (((TMRcvPrepared(rm) \/ RMPrepare(rm)) \/ RMChooseToAbort(rm))
          \/ (RMRcvCommitMsg(rm) \/ RMRcvAbortMsg(rm))))

TPSpec == Init /\ []([Next]_<<rmState, tmState, tmPrepared, msgs>>)

P == TPTypeOK /\ TCConsistent

Inv == TRUE /\ TPTypeOK

================================================================================
