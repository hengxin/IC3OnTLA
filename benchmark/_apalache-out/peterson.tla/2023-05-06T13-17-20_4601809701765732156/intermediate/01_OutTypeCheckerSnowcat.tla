----------------------- MODULE 01_OutTypeCheckerSnowcat -----------------------

EXTENDS Integers, Sequences, FiniteSets, TLC, Apalache

CONSTANT
  (*
    @type: Set(PROCSET);
  *)
  ProcSet

VARIABLE
  (*
    @type: (PROCSET -> Bool);
  *)
  flag

VARIABLE
  (*
    @type: (PROCSET -> Str);
  *)
  pc

VARIABLE
  (*
    @type: PROCSET;
  *)
  turn

(*
  @type: ((a232, a233) => (a232 -> a233));
*)
:>(__key, __value) == [ __x \in {__key} |-> __value ]

(*
  @type: (((a211 -> a212), (a211 -> a212)) => (a211 -> a212));
*)
@@(__f1, __f2) ==
  LET (*@type: (() => (a211 -> a212)); *) __f1_cache == __f1 IN
  LET (*@type: (() => (a211 -> a212)); *) __f2_cache == __f2 IN
  LET (*@type: (() => Set(a211)); *) __d1 == DOMAIN __f1_cache IN
  LET (*@type: (() => Set(a211)); *) __d2 == DOMAIN __f2_cache IN
  [
    __x \in __d1 \union __d2 |->
      IF __x \in __d1 THEN (__f1_cache)[__x] ELSE (__f2_cache)[__x]
  ]

(*
  @type: ((Str, a207) => a207);
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
  @type: ((Int) => a198);
*)
TLCGet(__i) ==
  LET (*@type: (() => Set(a200)); *) __Empty == {} IN
  CHOOSE __x \in __Empty: TRUE

(*
  @type: ((Int, a195) => Bool);
*)
TLCSet(__i, __v) == TRUE

(*
  @type: ((Set(a185)) => Set((a185 -> a185)));
*)
Permutations(__S) ==
  { __f \in [__S -> __S]: \A __w \in __S: \E __v \in __S: __f[__v] = __w }

(*
  @type: ((Set(a182)) => a182);
*)
RandomElement(__s) == CHOOSE __x \in __s: TRUE

(*
  @type: (() => a176);
*)
Any ==
  LET (*@type: (() => Set(a178)); *) __Empty == {} IN
  CHOOSE __x \in __Empty: TRUE

(*
  @type: ((a174) => Str);
*)
ToString(__v) == ""

(*
  @type: ((a172) => a172);
*)
TLCEval(__v) == __v

(*
  @type: ((Seq(a125), ((a125, a125) => Bool)) => (Int -> a125));
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
  @type: (() => <<(PROCSET -> Bool), PROCSET, (PROCSET -> Str)>>);
*)
vars == <<flag, turn, pc>>

(*
  @type: ((PROCSET) => PROCSET);
*)
Other(p) == CHOOSE q \in ProcSet: q /= p

(*
  @type: (() => Bool);
*)
Init ==
  flag = [ proc \in ProcSet |-> FALSE ]
    /\ turn \in ProcSet
    /\ pc = [ self \in ProcSet |-> "a1" ]

(*
  @type: ((PROCSET) => Bool);
*)
a1(self) ==
  pc[self] = "a1"
    /\ TRUE
    /\ pc' = [ pc EXCEPT ![self] = "a2" ]
    /\ UNCHANGED (<<flag, turn>>)

(*
  @type: ((PROCSET) => Bool);
*)
a2(self) ==
  pc[self] = "a2"
    /\ flag' = [ flag EXCEPT ![self] = TRUE ]
    /\ pc' = [ pc EXCEPT ![self] = "a3" ]
    /\ turn' = turn

(*
  @type: ((PROCSET, PROCSET) => Bool);
*)
a3(self, other) ==
  ((((pc[self] = "a3") /\ self /= other) /\ turn' = other)
      /\ pc' = [ pc EXCEPT ![self] = "a4" ])
    /\ flag' = flag

(*
  @type: ((PROCSET, PROCSET) => Bool);
*)
a4(self, other) ==
  self /= other
    /\ pc[self] = "a4"
    /\ (flag[other] = FALSE \/ turn = self)
    /\ pc' = [ pc EXCEPT ![self] = "cs" ]
    /\ UNCHANGED (<<flag, turn>>)

(*
  @type: ((PROCSET) => Bool);
*)
cs(self) ==
  pc[self] = "cs"
    /\ TRUE
    /\ pc' = [ pc EXCEPT ![self] = "a5" ]
    /\ UNCHANGED (<<flag, turn>>)

(*
  @type: ((PROCSET) => Bool);
*)
a5(self) ==
  pc[self] = "a5"
    /\ flag' = [ flag EXCEPT ![self] = FALSE ]
    /\ pc' = [ pc EXCEPT ![self] = "a1" ]
    /\ turn' = turn

(*
  @type: (() => Bool);
*)
Mutex ==
  \A p \in ProcSet: \A q \in ProcSet: p /= q => ~(pc[p] = "cs" /\ pc[q] = "cs")

(*
  @type: (() => Set((PROCSET -> PROCSET)));
*)
Symmetry == Permutations(ProcSet)

(*
  @type: (() => Bool);
*)
TypeOK ==
  flag \in [ProcSet -> BOOLEAN]
    /\ turn \in ProcSet
    /\ pc \in [ProcSet -> { "a1", "a2", "a3", "a4", "a5", "cs" }]

(*
  @type: (() => Bool);
*)
InitializeProcSet == ProcSet = { "p0_OF_PROCSET", "p1_OF_PROCSET" }

(*
  @type: (() => Bool);
*)
ASSUME(Cardinality(ProcSet) = 2)

(*
  @type: (() => Bool);
*)
Next ==
  \E self \in ProcSet:
    \E other \in ProcSet:
      a1(self)
        \/ a2(self)
        \/ a3(self, other)
        \/ a4(self, other)
        \/ cs(self)
        \/ a5(self)

(*
  @type: (() => Bool);
*)
NextUnchanged == UNCHANGED vars

(*
  @type: (() => Bool);
*)
P == TypeOK /\ Mutex

(*
  @type: (() => Bool);
*)
Spec == (Init /\ []([Next]_vars))

================================================================================
