--------------------------- MODULE 07_OutPrimingPass ---------------------------

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
  @type: (() => Set(VALUE));
*)
InitializeVALUE == { "v1_OF_VALUE", "v2_OF_VALUE", "v3_OF_VALUE" }

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
Inv == (chosen \in SUBSET Value) /\ Cardinality(chosen) <= 1

InitializeVALUEPrimed == { "v1_OF_VALUE", "v2_OF_VALUE", "v3_OF_VALUE" }

InitPrimed == chosen' = {}

================================================================================
