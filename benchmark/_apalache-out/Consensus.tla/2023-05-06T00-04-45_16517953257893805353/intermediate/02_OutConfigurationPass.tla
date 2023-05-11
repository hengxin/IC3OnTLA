------------------------ MODULE 02_OutConfigurationPass ------------------------

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
TypeOK == chosen \in SUBSET Value

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
Next == chosen = {} /\ (\E v \in Value: chosen' = {v})

(*
  @type: (() => Bool);
*)
Success == <>(chosen /= {})

(*
  @type: (() => Bool);
*)
Spec == Init /\ []([Next]_chosen)

(*
  @type: (() => Bool);
*)
Inv == TypeOK /\ Cardinality(chosen) <= 1

(*
  @type: (() => Bool);
*)
NOTInv == ~TypeOK

(*
  @type: (() => Bool);
*)
LiveSpec == Spec /\ WF_chosen(Next)

================================================================================
