----------------------- MODULE 01_OutTypeCheckerSnowcat -----------------------

EXTENDS Integers, Sequences, FiniteSets, TLC, Apalache

CONSTANT
  (*
    @type: Set(RM);
  *)
  RM

VARIABLE
  (*
    @type: Set([rm: RM, type: Str]);
  *)
  msgs

VARIABLE
  (*
    @type: (RM -> Str);
  *)
  rmState

VARIABLE
  (*
    @type: Str;
  *)
  tmState

VARIABLE
  (*
    @type: Set(RM);
  *)
  tmPrepared

(*
  @type: (() => Bool);
*)
Inv == TRUE

(*
  @type: (() => Set([rm: RM, type: Str]));
*)
Message ==
  { [type |-> t, rm |-> r]: t \in {"Prepared"}, r \in RM }
    \union { [type |-> t]: t \in { "Commit", "Abort" } }

(*
  @type: (() => Bool);
*)
InitializeRM == RM = { "r1_OF_RM", "r2_OF_RM" }

(*
  @type: (() => Bool);
*)
Init ==
  rmState = [ rm \in RM |-> "working" ]
    /\ tmState = "init"
    /\ tmPrepared = {}
    /\ msgs = {}

(*
  @type: ((RM) => Bool);
*)
TMRcvPrepared(rm) ==
  tmState = "init"
    /\ [type |-> "Prepared", rm |-> rm] \in msgs
    /\ tmPrepared' = tmPrepared \union {rm}
    /\ UNCHANGED (<<rmState, tmState, msgs>>)

(*
  @type: (() => Bool);
*)
TMCommit ==
  tmState = "init"
    /\ tmPrepared = RM
    /\ tmState' = "committed"
    /\ msgs' = msgs \union {[type |-> "Commit"]}
    /\ UNCHANGED (<<rmState, tmPrepared>>)

(*
  @type: (() => Bool);
*)
TMAbort ==
  tmState = "init"
    /\ tmState' = "aborted"
    /\ msgs' = msgs \union {[type |-> "Abort"]}
    /\ UNCHANGED (<<rmState, tmPrepared>>)

(*
  @type: ((RM) => Bool);
*)
RMPrepare(rm) ==
  rmState[rm] = "working"
    /\ rmState' = [ rmState EXCEPT ![rm] = "prepared" ]
    /\ msgs' = msgs \union {[type |-> "Prepared", rm |-> rm]}
    /\ UNCHANGED (<<tmState, tmPrepared>>)

(*
  @type: ((RM) => Bool);
*)
RMChooseToAbort(rm) ==
  rmState[rm] = "working"
    /\ rmState' = [ rmState EXCEPT ![rm] = "aborted" ]
    /\ UNCHANGED (<<tmState, tmPrepared, msgs>>)

(*
  @type: ((RM) => Bool);
*)
RMRcvCommitMsg(rm) ==
  [type |-> "Commit"] \in msgs
    /\ rmState' = [ rmState EXCEPT ![rm] = "committed" ]
    /\ UNCHANGED (<<tmState, tmPrepared, msgs>>)

(*
  @type: ((RM) => Bool);
*)
RMRcvAbortMsg(rm) ==
  [type |-> "Abort"] \in msgs
    /\ rmState' = [ rmState EXCEPT ![rm] = "aborted" ]
    /\ UNCHANGED (<<tmState, tmPrepared, msgs>>)

(*
  @type: (() => Bool);
*)
TCConsistent ==
  \A rm1 \in RM:
    \A rm2 \in RM: ~(rmState[rm1] = "aborted" /\ rmState[rm2] = "committed")

(*
  @type: (() => Bool);
*)
TPTypeOK ==
  rmState \in [RM -> { "working", "prepared", "committed", "aborted" }]
    /\ tmState \in { "init", "committed", "aborted" }
    /\ tmPrepared \in SUBSET RM
    /\ msgs \in SUBSET Message

(*
  @type: (() => Bool);
*)
Next ==
  (TMCommit \/ TMAbort)
    \/ (\E rm \in RM:
      (((TMRcvPrepared(rm) \/ RMPrepare(rm)) \/ RMChooseToAbort(rm))
          \/ (RMRcvCommitMsg(rm) \/ RMRcvAbortMsg(rm))))

(*
  @type: (() => Bool);
*)
TPSpec == Init /\ []([Next]_<<rmState, tmState, tmPrepared, msgs>>)

(*
  @type: (() => Bool);
*)
P == TPTypeOK /\ TCConsistent

================================================================================
