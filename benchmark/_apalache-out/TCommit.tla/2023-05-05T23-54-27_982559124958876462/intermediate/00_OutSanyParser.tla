--------------------------- MODULE 00_OutSanyParser ---------------------------

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

TCTypeOK ==
  rmState \in [RM -> { "working", "prepared", "committed", "aborted" }]

Init == rmState = [ rm \in RM |-> "working" ]

(*
  ***********************************************************************
 The initial predicate.                                                
***********************************************************************
*)
canCommit == \A rm \in RM: rmState[rm] \in { "prepared", "committed" }

(*
  ***********************************************************************
 True iff all RMs are in the "prepared" or "committed" state.          
***********************************************************************
*)
notCommitted == \A rm \in RM: rmState[rm] /= "committed"

(*
  *************************************************************************
 We now define the actions that may be performed by the RMs, and then    
 define the complete next-state action of the specification to be the    
 disjunction of the possible RM actions.                                 
*************************************************************************
*)
Prepare(rm) ==
  rmState[rm] = "working" /\ rmState' = [ rmState EXCEPT ![rm] = "prepared" ]

(*
  *************************************************************************
 We now assert invariance properties of the specification.               
*************************************************************************
*)
TCConsistent ==
  \A rm1 \in RM:
    \A rm2 \in RM: ~(rmState[rm1] = "aborted" /\ rmState[rm2] = "committed")

(*
  ***********************************************************************
 Asserts that TCTypeOK and TCConsistent are invariants of the protocol. 
***********************************************************************
*)
Symmetry == Permutations(RM)

InitializeRM == RM = { "r1_OF_RM", "r2_OF_RM", "r3_OF_RM" }

Decide(rm) ==
  (rmState[rm] = "prepared"
      /\ canCommit
      /\ rmState' = [ rmState EXCEPT ![rm] = "committed" ])
    \/ (rmState[rm] \in { "working", "prepared" }
      /\ notCommitted
      /\ rmState' = [ rmState EXCEPT ![rm] = "aborted" ])

P == TCTypeOK /\ TCConsistent

NOTP == ~TCTypeOK

Next == \E rm \in RM: Prepare(rm) \/ Decide(rm)

TCSpec == Init /\ []([Next]_rmState)

================================================================================
