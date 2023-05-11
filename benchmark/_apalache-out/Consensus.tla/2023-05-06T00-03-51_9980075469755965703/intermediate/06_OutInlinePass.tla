--------------------------- MODULE 06_OutInlinePass ---------------------------

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

================================================================================
