------------------------ MODULE 11_OutOptimizationPass ------------------------

EXTENDS Integers, Sequences, FiniteSets, TLC, Apalache

CONSTANT
  (*
    @type: Set(RM);
  *)
  RM

VARIABLE
  (*
    @type: (RM -> Str);
  *)
  rmState

(*
  @type: (() => Bool);
*)
CInit_si_0 == RM' := { "r1_OF_RM", "r2_OF_RM", "r3_OF_RM" }

(*
  @type: (() => Bool);
*)
Init_si_0000 ==
  (\E t_3$1 \in [RM -> { "working", "prepared", "committed", "aborted" }]:
      rmState' := t_3$1)
    /\ (\A rm1$1 \in RM:
      \A rm2$1 \in RM:
        ~(rmState'[rm1$1] = "aborted") \/ ~(rmState'[rm2$1] = "committed"))

(*
  @type: (() => Bool);
*)
Next_si_0000 ==
  \E rm$1 \in RM:
    rmState[rm$1] = "working"
      /\ rmState' := [ rmState EXCEPT ![rm$1] = "prepared" ]

(*
  @type: (() => Bool);
*)
Next_si_0001 ==
  \E rm$2 \in RM:
    rmState[rm$2] = "prepared"
      /\ (\A rm$3 \in RM: rmState[rm$3] \in { "prepared", "committed" })
      /\ rmState' := [ rmState EXCEPT ![rm$2] = "committed" ]

(*
  @type: (() => Bool);
*)
Next_si_0002 ==
  \E rm$4 \in RM:
    rmState[rm$4] \in { "working", "prepared" }
      /\ (\A rm$5 \in RM: ~(rmState[rm$5] = "committed"))
      /\ rmState' := [ rmState EXCEPT ![rm$4] = "aborted" ]

(*
  @type: Bool;
*)
VCInv_si_0 ==
  ~(DOMAIN rmState = RM
    /\ (\A t_4$1 \in RM:
      rmState[t_4$1] \in { "working", "prepared", "committed", "aborted" }))

(*
  @type: Bool;
*)
VCNotInv_si_0 ==
  DOMAIN rmState = RM
    /\ (\A t_5$1 \in RM:
      rmState[t_5$1] \in { "working", "prepared", "committed", "aborted" })

================================================================================
