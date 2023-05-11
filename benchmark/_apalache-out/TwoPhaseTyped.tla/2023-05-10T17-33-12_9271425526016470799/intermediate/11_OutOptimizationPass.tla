------------------------ MODULE 11_OutOptimizationPass ------------------------

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
  (\E t_3$1 \in [RM -> { "working", "prepared", "committed", "aborted" }]:
      rmState' := t_3$1)
    /\ (\E t_4$1 \in { "init", "committed", "aborted" }: tmState' := t_4$1)
    /\ (\E t_5$1 \in SUBSET RM: tmPrepared' := t_5$1)
    /\ (\E t_6$1 \in SUBSET ({
      [type |-> t$1, rm |-> r$1]:
        t$1 \in {"Prepared"},
        r$1 \in RM
    }
      \union { [type |-> t$2]: t$2 \in { "Commit", "Abort" } }):
      msgs' := t_6$1)

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
  \E rm$1 \in RM:
    rmState[rm$1] = "working"
      /\ rmState' := [ rmState EXCEPT ![rm$1] = "prepared" ]
      /\ msgs' := (msgs \union {[type |-> "Prepared", rm |-> rm$1]})
      /\ (tmState' := tmState /\ tmPrepared' := tmPrepared)

(*
  @type: (() => Bool);
*)
Next_si_0003 ==
  \E rm$2 \in RM:
    [type |-> "Commit"] \in msgs
      /\ rmState' := [ rmState EXCEPT ![rm$2] = "committed" ]
      /\ (tmState' := tmState /\ tmPrepared' := tmPrepared /\ msgs' := msgs)

(*
  @type: (() => Bool);
*)
Next_si_0004 ==
  \E rm$3 \in RM:
    [type |-> "Abort"] \in msgs
      /\ rmState' := [ rmState EXCEPT ![rm$3] = "aborted" ]
      /\ (tmState' := tmState /\ tmPrepared' := tmPrepared /\ msgs' := msgs)

(*
  @type: (() => Bool);
*)
Next_si_0005 ==
  \E rm$4 \in RM:
    rmState[rm$4] = "working"
      /\ rmState' := [ rmState EXCEPT ![rm$4] = "aborted" ]
      /\ (tmState' := tmState /\ tmPrepared' := tmPrepared /\ msgs' := msgs)

(*
  @type: (() => Bool);
*)
Next_si_0006 ==
  \E rm$5 \in RM:
    tmState = "init"
      /\ [type |-> "Prepared", rm |-> rm$5] \in msgs
      /\ tmPrepared' := (tmPrepared \union {rm$5})
      /\ (rmState' := rmState /\ tmState' := tmState /\ msgs' := msgs)

(*
  @type: Bool;
*)
VCInv_si_0 ==
  DOMAIN rmState = RM
    /\ (\A t_7$1 \in RM:
      rmState[t_7$1] \in { "working", "prepared", "committed", "aborted" })

(*
  @type: Bool;
*)
VCNotInv_si_0 ==
  ~(DOMAIN rmState = RM
    /\ (\A t_8$1 \in RM:
      rmState[t_8$1] \in { "working", "prepared", "committed", "aborted" }))

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
    \in SUBSET ({ [type |-> t$3, rm |-> r$2]: t$3 \in {"Prepared"}, r$2 \in RM }
      \union { [type |-> t$4]: t$4 \in { "Commit", "Abort" } })

(*
  @type: Bool;
*)
VCNotInv_si_3 ==
  ~(msgs
    \in SUBSET ({ [type |-> t$5, rm |-> r$3]: t$5 \in {"Prepared"}, r$3 \in RM }
      \union { [type |-> t$6]: t$6 \in { "Commit", "Abort" } }))

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
  \E rm1$2 \in RM:
    \E rm2$2 \in RM: rmState[rm1$2] = "aborted" /\ rmState[rm2$2] = "committed"

================================================================================
