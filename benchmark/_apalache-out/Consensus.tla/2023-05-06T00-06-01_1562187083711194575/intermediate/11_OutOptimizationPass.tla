------------------------ MODULE 11_OutOptimizationPass ------------------------

EXTENDS Integers, Sequences, FiniteSets, TLC, Apalache

CONSTANT
  (*
    @type: Set(VALUE);
  *)
  Value

VARIABLE
  (*
    @type: Set(VALUE);
  *)
  chosen

(*
  @type: (() => Bool);
*)
CInit_si_0 == Value' := { "v1_OF_VALUE", "v2_OF_VALUE", "v3_OF_VALUE" }

(*
  @type: (() => Bool);
*)
Init_si_0000 == chosen' := {}

(*
  @type: (() => Bool);
*)
Next_si_0000 == chosen = {} /\ (\E v$1 \in Value: chosen' := {v$1})

(*
  @type: Bool;
*)
VCInv_si_0 == ~(chosen \in SUBSET Value)

(*
  @type: Bool;
*)
VCNotInv_si_0 == chosen \in SUBSET Value

================================================================================
