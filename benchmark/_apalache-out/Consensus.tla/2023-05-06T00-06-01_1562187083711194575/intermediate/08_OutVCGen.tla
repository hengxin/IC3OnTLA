------------------------------ MODULE 08_OutVCGen ------------------------------

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
InitializeVALUE == Value = { "v1_OF_VALUE", "v2_OF_VALUE", "v3_OF_VALUE" }

(*
  @type: (() => Bool);
*)
Init == chosen = {}

(*
  @type: (() => Bool);
*)
Next == chosen = {} /\ (\E v$1 \in Value: chosen' = {v$1})

(*
  @type: (() => Bool);
*)
NOTInv == ~(chosen \in SUBSET Value)

InitializeVALUEPrimed ==
  Value' = { "v1_OF_VALUE", "v2_OF_VALUE", "v3_OF_VALUE" }

InitPrimed == chosen' = {}

(*
  @type: Bool;
*)
VCInv_si_0 == ~(chosen \in SUBSET Value)

(*
  @type: Bool;
*)
VCNotInv_si_0 == ~(~(chosen \in SUBSET Value))

================================================================================
