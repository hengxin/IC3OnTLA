-------------------------- MODULE 05_OutTemporalPass --------------------------

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
InitializeRM == RM = { "r1_OF_RM", "r2_OF_RM", "r3_OF_RM" }

(*
  @type: (() => Bool);
*)
P ==
  rmState \in [RM -> { "working", "prepared", "committed", "aborted" }]
    /\ (\A rm1$2 \in RM:
      \A rm2$2 \in RM:
        ~(rmState[rm1$2] = "aborted" /\ rmState[rm2$2] = "committed"))

(*
  @type: (() => Bool);
*)
NOTP == ~(rmState \in [RM -> { "working", "prepared", "committed", "aborted" }])

(*
  @type: (() => Bool);
*)
Next ==
  \E rm$4 \in RM:
    (rmState[rm$4] = "working"
        /\ rmState' = [ rmState EXCEPT ![rm$4] = "prepared" ])
      \/ ((rmState[rm$4] = "prepared"
          /\ (\A rm$7 \in RM: rmState[rm$7] \in { "prepared", "committed" })
          /\ rmState' = [ rmState EXCEPT ![rm$4] = "committed" ])
        \/ (rmState[rm$4] \in { "working", "prepared" }
          /\ (\A rm$8 \in RM: rmState[rm$8] /= "committed")
          /\ rmState' = [ rmState EXCEPT ![rm$4] = "aborted" ]))

================================================================================
