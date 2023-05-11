--------------------------- MODULE 00_OutSanyParser ---------------------------

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
  The famous smiley operator.
  @type: (a, b) => (a -> b);
*)
:>(__key, __value) == [ __x \in {__key} |-> __value ]

(*
  Function composition (fun-fun).
  @type: (a -> b, a -> b) => (a -> b);
*)
@@(__f1, __f2) ==
  LET __f1_cache == __f1 IN
  LET __f2_cache == __f2 IN
  LET __d1 == DOMAIN __f1_cache IN
  LET __d2 == DOMAIN __f2_cache IN
  [
    __x \in __d1 \union __d2 |->
      IF __x \in __d1 THEN (__f1_cache)[__x] ELSE (__f2_cache)[__x]
  ]

(*
  Print is doing nothing in Apalache.
  @type: (Str, a) => a;
*)
Print(__out, __val) == __val

(*
  Print is doing nothing in Apalache.
  @type: Str => Bool;
*)
PrintT(__out) == TRUE

(*
  In Apalache, assert is side-effect free.
 It never produces an error, even if the condition is false.
  @type: (Bool, Str) => Bool;
*)
Assert(__cond, __out) == __cond

(*
  Apalache does not support this operator, but the type checker does.
  @type: () => Int;
*)
JavaTime == 123

(*
  Apalache does not support this operator, but the type checker does.
  @type: Int => a;
*)
TLCGet(__i) ==
  LET (*@type: () => Set(a); *) __Empty == {} IN CHOOSE __x \in __Empty: TRUE

(*
  Apalache does not support this operator, but the type checker does.
  @type: (Int, a) => Bool;
*)
TLCSet(__i, __v) == TRUE

(*
  @type: Set(a) => Set(a -> a);
*)
Permutations(__S) ==
  { __f \in [__S -> __S]: \A __w \in __S: \E __v \in __S: __f[__v] = __w }

(*
  Obviously, we cannot do randomization in Apalache.
  @type: Set(a) => a;
*)
RandomElement(__s) == CHOOSE __x \in __s: TRUE

(*
  Most likely, the type checker will fail on that one more often than it will work.
  @type: () => a;
*)
Any ==
  LET (*@type: () => Set(a); *) __Empty == {} IN CHOOSE __x \in __Empty: TRUE

(*
  @type: a => Str;
*)
ToString(__v) == ""

(*
  For type compatibility with TLC.
  @type: a => a;
*)
TLCEval(__v) == __v

(*
  We return the function instead of a sequence, because that is what it returns.
  @type: (Seq(a), (a, a) => Bool) => (Int -> a);
*)
SortSeq(__s, __Op(_, _)) ==
  LET __Perm ==
    CHOOSE __p \in Permutations((DOMAIN __s)):
      \A __i \in DOMAIN __s:
        \A __j \in DOMAIN __s:
          (__i < __j => __Op(__s[__p[__i]], __s[__p[__j]]))
            \/ __s[__p[__i]] = __s[__p[__j]]
  IN
  [ __i \in DOMAIN __s |-> __s[(__Perm)[__i]] ]

(*
  The program counter for each process.
*)
vars == <<flag, turn, pc>>

(*
  Return the other process.
*)
Other(p) == CHOOSE q \in ProcSet: q /= p

Init ==
  flag = [ proc \in ProcSet |-> FALSE ]
    /\ turn \in ProcSet
    /\ pc = [ self \in ProcSet |-> "a1" ]

(*
  The transitions of the protocol.
*)
a1(self) ==
  pc[self] = "a1"
    /\ TRUE
    /\ pc' = [ pc EXCEPT ![self] = "a2" ]
    /\ UNCHANGED (<<flag, turn>>)

(*
  A process sets its own flag to TRUE.
*)
a2(self) ==
  pc[self] = "a2"
    /\ flag' = [ flag EXCEPT ![self] = TRUE ]
    /\ pc' = [ pc EXCEPT ![self] = "a3" ]
    /\ turn' = turn

(*
  A process updates 'turn'.
*)
a3(self, other) ==
  ((((pc[self] = "a3") /\ self /= other) /\ turn' = other)
      /\ pc' = [ pc EXCEPT ![self] = "a4" ])
    /\ flag' = flag

(*
  A process enters the critical section.
*)
a4(self, other) ==
  self /= other
    /\ pc[self] = "a4"
    /\ (flag[other] = FALSE \/ turn = self)
    /\ pc' = [ pc EXCEPT ![self] = "cs" ]
    /\ UNCHANGED (<<flag, turn>>)

(*
  A process exits the critical section.
*)
cs(self) ==
  pc[self] = "cs"
    /\ TRUE
    /\ pc' = [ pc EXCEPT ![self] = "a5" ]
    /\ UNCHANGED (<<flag, turn>>)

(*
  A process resets its own flag to FALSE after it left the critical section.
*)
a5(self) ==
  pc[self] = "a5"
    /\ flag' = [ flag EXCEPT ![self] = FALSE ]
    /\ pc' = [ pc EXCEPT ![self] = "a1" ]
    /\ turn' = turn

(*
  The mutual exclusion property i.e. the processes cannot be 
 inside the critical sectuion at the same time.
*)
Mutex ==
  \A p \in ProcSet: \A q \in ProcSet: p /= q => ~(pc[p] = "cs" /\ pc[q] = "cs")

Symmetry == Permutations(ProcSet)

TypeOK ==
  flag \in [ProcSet -> BOOLEAN]
    /\ turn \in ProcSet
    /\ pc \in [ProcSet -> { "a1", "a2", "a3", "a4", "a5", "cs" }]

InitializeProcSet == ProcSet = { "p0_OF_PROCSET", "p1_OF_PROCSET" }

ASSUME(Cardinality(ProcSet) = 2)

Next ==
  \E self \in ProcSet:
    \E other \in ProcSet:
      a1(self)
        \/ a2(self)
        \/ a3(self, other)
        \/ a4(self, other)
        \/ cs(self)
        \/ a5(self)

NextUnchanged == UNCHANGED vars

P == TypeOK /\ Mutex

Spec == (Init /\ []([Next]_vars))

================================================================================
