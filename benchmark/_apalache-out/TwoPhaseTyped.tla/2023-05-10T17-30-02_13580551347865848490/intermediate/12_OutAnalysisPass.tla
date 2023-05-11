-------------------------- MODULE 12_OutAnalysisPass --------------------------

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
CInit_si_0 == RM' := { "r1_OF_RM", "r2_OF_RM" }

(*
  @type: (() => Bool);
*)
Init_si_0000 ==
  rmState' := [ rm$1 \in RM |-> "working" ]
    /\ tmState' := "init"
    /\ tmPrepared' := {}
    /\ msgs' := {}

(*
  @type: (() => Bool);
*)
Next_si_0000 ==
  tmState = "init"
    /\ tmPrepared = RM
    /\ tmState' := "committed"
    /\ msgs' := (msgs \union {[type |-> "Commit"]})
    /\ (rmState' := rmState /\ tmPrepared' := tmPrepared)

(*
  @type: (() => Bool);
*)
Next_si_0001 ==
  tmState = "init"
    /\ tmState' := "aborted"
    /\ msgs' := (msgs \union {[type |-> "Abort"]})
    /\ (rmState' := rmState /\ tmPrepared' := tmPrepared)

(*
  @type: (() => Bool);
*)
Next_si_0002 ==
  Skolem((\E rm$2 \in RM:
    [type |-> "Abort"] \in msgs
      /\ rmState' := [ rmState EXCEPT ![rm$2] = "aborted" ]
      /\ (tmState' := tmState /\ tmPrepared' := tmPrepared /\ msgs' := msgs)))

(*
  @type: (() => Bool);
*)
Next_si_0003 ==
  Skolem((\E rm$3 \in RM:
    rmState[rm$3] = "working"
      /\ rmState' := [ rmState EXCEPT ![rm$3] = "prepared" ]
      /\ msgs' := (msgs \union {[type |-> "Prepared", rm |-> rm$3]})
      /\ (tmState' := tmState /\ tmPrepared' := tmPrepared)))

(*
  @type: (() => Bool);
*)
Next_si_0004 ==
  Skolem((\E rm$4 \in RM:
    rmState[rm$4] = "working"
      /\ rmState' := [ rmState EXCEPT ![rm$4] = "aborted" ]
      /\ (tmState' := tmState /\ tmPrepared' := tmPrepared /\ msgs' := msgs)))

(*
  @type: (() => Bool);
*)
Next_si_0005 ==
  Skolem((\E rm$5 \in RM:
    tmState = "init"
      /\ [type |-> "Prepared", rm |-> rm$5] \in msgs
      /\ tmPrepared' := (tmPrepared \union {rm$5})
      /\ (rmState' := rmState /\ tmState' := tmState /\ msgs' := msgs)))

(*
  @type: (() => Bool);
*)
Next_si_0006 ==
  Skolem((\E rm$6 \in RM:
    [type |-> "Commit"] \in msgs
      /\ rmState' := [ rmState EXCEPT ![rm$6] = "committed" ]
      /\ (tmState' := tmState /\ tmPrepared' := tmPrepared /\ msgs' := msgs)))

(*
  @type: Bool;
*)
VCInv_si_0 ==
  DOMAIN rmState = RM
    /\ (\A t_2$1 \in RM:
      rmState[t_2$1] \in { "working", "prepared", "committed", "aborted" })

(*
  @type: Bool;
*)
VCNotInv_si_0 ==
  ~(DOMAIN rmState = RM
    /\ (\A t_3$1 \in RM:
      rmState[t_3$1] \in { "working", "prepared", "committed", "aborted" }))

(*
  @type: Bool;
*)
VCInv_si_1 == tmState \in { "init", "committed", "aborted" }

(*
  @type: Bool;
*)
VCNotInv_si_1 == ~(tmState \in { "init", "committed", "aborted" })

(*
  @type: Bool;
*)
VCInv_si_2 == tmPrepared \in SUBSET RM

(*
  @type: Bool;
*)
VCNotInv_si_2 == ~(tmPrepared \in SUBSET RM)

(*
  @type: Bool;
*)
VCInv_si_3 ==
  msgs
    \in SUBSET ({ [type |-> t$1, rm |-> r$1]: t$1 \in {"Prepared"}, r$1 \in RM }
      \union { [type |-> t$2]: t$2 \in { "Commit", "Abort" } })

(*
  @type: Bool;
*)
VCNotInv_si_3 ==
  ~(msgs
    \in SUBSET ({ [type |-> t$3, rm |-> r$2]: t$3 \in {"Prepared"}, r$2 \in RM }
      \union { [type |-> t$4]: t$4 \in { "Commit", "Abort" } }))

(*
  @type: Bool;
*)
VCInv_si_4 ==
  \A rm1$1 \in RM:
    \A rm2$1 \in RM:
      ~(rmState[rm1$1] = "aborted") \/ ~(rmState[rm2$1] = "committed")

(*
  @type: Bool;
*)
VCNotInv_si_4 ==
  Skolem((\E rm1$2 \in RM:
    Skolem((\E rm2$2 \in RM:
      rmState[rm1$2] = "aborted" /\ rmState[rm2$2] = "committed"))))

================================================================================
