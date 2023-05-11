------------------------ MODULE 09_OutPreprocessingPass ------------------------

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
InitializeRM == RM = { "r1_OF_RM", "r2_OF_RM" }

(*
  @type: (() => Bool);
*)
Init ==
  rmState = [ rm$1 \in RM |-> "working" ]
    /\ tmState = "init"
    /\ tmPrepared = {}
    /\ msgs = {}

(*
  @type: (() => Bool);
*)
Next ==
  ((tmState = "init"
        /\ tmPrepared = RM
        /\ tmState' = "committed"
        /\ msgs' = msgs \union {[type |-> "Commit"]}
        /\ (rmState' := rmState /\ tmPrepared' := tmPrepared))
      \/ (tmState = "init"
        /\ tmState' = "aborted"
        /\ msgs' = msgs \union {[type |-> "Abort"]}
        /\ (rmState' := rmState /\ tmPrepared' := tmPrepared)))
    \/ (\E rm$2 \in RM:
      ((((tmState = "init"
                /\ [type |-> "Prepared", rm |-> rm$2] \in msgs
                /\ tmPrepared' = tmPrepared \union {rm$2}
                /\ (rmState' := rmState /\ tmState' := tmState /\ msgs' := msgs))
              \/ (rmState[rm$2] = "working"
                /\ rmState' = [ rmState EXCEPT ![rm$2] = "prepared" ]
                /\ msgs' = msgs \union {[type |-> "Prepared", rm |-> rm$2]}
                /\ (tmState' := tmState /\ tmPrepared' := tmPrepared)))
            \/ (rmState[rm$2] = "working"
              /\ rmState' = [ rmState EXCEPT ![rm$2] = "aborted" ]
              /\ (tmState' := tmState
                /\ tmPrepared' := tmPrepared
                /\ msgs' := msgs)))
          \/ (([type |-> "Commit"] \in msgs
              /\ rmState' = [ rmState EXCEPT ![rm$2] = "committed" ]
              /\ (tmState' := tmState
                /\ tmPrepared' := tmPrepared
                /\ msgs' := msgs))
            \/ ([type |-> "Abort"] \in msgs
              /\ rmState' = [ rmState EXCEPT ![rm$2] = "aborted" ]
              /\ (tmState' := tmState
                /\ tmPrepared' := tmPrepared
                /\ msgs' := msgs)))))

(*
  @type: (() => Bool);
*)
P ==
  ((DOMAIN rmState = RM
        /\ (\A t_1$1 \in RM:
          rmState[t_1$1] \in { "working", "prepared", "committed", "aborted" }))
      /\ tmState \in { "init", "committed", "aborted" }
      /\ tmPrepared \in SUBSET RM
      /\ msgs
        \in SUBSET ({
          [type |-> t$1, rm |-> r$1]:
            t$1 \in {"Prepared"},
            r$1 \in RM
        }
          \union { [type |-> t$2]: t$2 \in { "Commit", "Abort" } }))
    /\ (\A rm1$1 \in RM:
      \A rm2$1 \in RM:
        ~(rmState[rm1$1] = "aborted") \/ ~(rmState[rm2$1] = "committed"))

InitializeRMPrimed == RM' = { "r1_OF_RM", "r2_OF_RM" }

InitPrimed ==
  rmState' = [ rm$3 \in RM |-> "working" ]
    /\ tmState' = "init"
    /\ tmPrepared' = {}
    /\ msgs' = {}

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
  \A rm1$2 \in RM:
    \A rm2$2 \in RM:
      ~(rmState[rm1$2] = "aborted") \/ ~(rmState[rm2$2] = "committed")

(*
  @type: Bool;
*)
VCNotInv_si_4 ==
  \E rm1$3 \in RM:
    \E rm2$3 \in RM: rmState[rm1$3] = "aborted" /\ rmState[rm2$3] = "committed"

================================================================================
