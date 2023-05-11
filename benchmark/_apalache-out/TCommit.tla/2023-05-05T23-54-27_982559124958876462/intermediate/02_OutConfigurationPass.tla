------------------------ MODULE 02_OutConfigurationPass ------------------------

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
  @type: ((a163, a164) => (a163 -> a164));
*)
:>(__key, __value) == [ __x \in {__key} |-> __value ]

(*
  @type: (((a142 -> a143), (a142 -> a143)) => (a142 -> a143));
*)
@@(__f1, __f2) ==
  LET (*@type: (() => (a142 -> a143)); *) __f1_cache == __f1 IN
  LET (*@type: (() => (a142 -> a143)); *) __f2_cache == __f2 IN
  LET (*@type: (() => Set(a142)); *) __d1 == DOMAIN __f1_cache IN
  LET (*@type: (() => Set(a142)); *) __d2 == DOMAIN __f2_cache IN
  [
    __x \in __d1 \union __d2 |->
      IF __x \in __d1 THEN (__f1_cache)[__x] ELSE (__f2_cache)[__x]
  ]

(*
  @type: ((Str, a138) => a138);
*)
Print(__out, __val) == __val

(*
  @type: ((Str) => Bool);
*)
PrintT(__out) == TRUE

(*
  @type: ((Bool, Str) => Bool);
*)
Assert(__cond, __out) == __cond

(*
  @type: (() => Int);
*)
JavaTime == 123

(*
  @type: ((Int) => a129);
*)
TLCGet(__i) ==
  LET (*@type: (() => Set(a131)); *) __Empty == {} IN
  CHOOSE __x \in __Empty: TRUE

(*
  @type: ((Int, a126) => Bool);
*)
TLCSet(__i, __v) == TRUE

(*
  @type: ((Set(a116)) => Set((a116 -> a116)));
*)
Permutations(__S) ==
  { __f \in [__S -> __S]: \A __w \in __S: \E __v \in __S: __f[__v] = __w }

(*
  @type: ((Set(a113)) => a113);
*)
RandomElement(__s) == CHOOSE __x \in __s: TRUE

(*
  @type: (() => a107);
*)
Any ==
  LET (*@type: (() => Set(a109)); *) __Empty == {} IN
  CHOOSE __x \in __Empty: TRUE

(*
  @type: ((a105) => Str);
*)
ToString(__v) == ""

(*
  @type: ((a103) => a103);
*)
TLCEval(__v) == __v

(*
  @type: ((Seq(a56), ((a56, a56) => Bool)) => (Int -> a56));
*)
SortSeq(__s, __Op(_, _)) ==
  LET (*
    @type: (() => (Int -> Int));
  *)
  __Perm ==
    CHOOSE __p \in Permutations((DOMAIN __s)):
      \A __i \in DOMAIN __s:
        \A __j \in DOMAIN __s:
          (__i < __j => __Op(__s[__p[__i]], __s[__p[__j]]))
            \/ __s[__p[__i]] = __s[__p[__j]]
  IN
  [ __i \in DOMAIN __s |-> __s[(__Perm)[__i]] ]

(*
  @type: (() => Bool);
*)
TCTypeOK ==
  rmState \in [RM -> { "working", "prepared", "committed", "aborted" }]

(*
  @type: (() => Bool);
*)
Init == rmState = [ rm \in RM |-> "working" ]

(*
  @type: (() => Bool);
*)
canCommit == \A rm \in RM: rmState[rm] \in { "prepared", "committed" }

(*
  @type: (() => Bool);
*)
notCommitted == \A rm \in RM: rmState[rm] /= "committed"

(*
  @type: ((RM) => Bool);
*)
Prepare(rm) ==
  rmState[rm] = "working" /\ rmState' = [ rmState EXCEPT ![rm] = "prepared" ]

(*
  @type: (() => Bool);
*)
TCConsistent ==
  \A rm1 \in RM:
    \A rm2 \in RM: ~(rmState[rm1] = "aborted" /\ rmState[rm2] = "committed")

(*
  @type: (() => Set((RM -> RM)));
*)
Symmetry == Permutations(RM)

(*
  @type: (() => Bool);
*)
InitializeRM == RM = { "r1_OF_RM", "r2_OF_RM", "r3_OF_RM" }

(*
  @type: ((RM) => Bool);
*)
Decide(rm) ==
  (rmState[rm] = "prepared"
      /\ canCommit
      /\ rmState' = [ rmState EXCEPT ![rm] = "committed" ])
    \/ (rmState[rm] \in { "working", "prepared" }
      /\ notCommitted
      /\ rmState' = [ rmState EXCEPT ![rm] = "aborted" ])

(*
  @type: (() => Bool);
*)
P == TCTypeOK /\ TCConsistent

(*
  @type: (() => Bool);
*)
NOTP == ~TCTypeOK

(*
  @type: (() => Bool);
*)
Next == \E rm \in RM: Prepare(rm) \/ Decide(rm)

(*
  @type: (() => Bool);
*)
TCSpec == Init /\ []([Next]_rmState)

================================================================================
