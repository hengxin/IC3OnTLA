----------------------- MODULE 01_OutTypeCheckerSnowcat -----------------------

EXTENDS Integers, Sequences, FiniteSets, TLC, Apalache

CONSTANT
  (*
    @type: Set(NODE);
  *)
  Node

VARIABLE
  (*
    @type: (NODE -> Bool);
  *)
  lock_msg

VARIABLE
  (*
    @type: Bool;
  *)
  server_holds_lock

VARIABLE
  (*
    @type: (NODE -> Bool);
  *)
  holds_lock

VARIABLE
  (*
    @type: (NODE -> Bool);
  *)
  grant_msg

VARIABLE
  (*
    @type: (NODE -> Bool);
  *)
  unlock_msg

(*
  @type: ((a234, a235) => (a234 -> a235));
*)
:>(__key, __value) == [ __x \in {__key} |-> __value ]

(*
  @type: (((a213 -> a214), (a213 -> a214)) => (a213 -> a214));
*)
@@(__f1, __f2) ==
  LET (*@type: (() => (a213 -> a214)); *) __f1_cache == __f1 IN
  LET (*@type: (() => (a213 -> a214)); *) __f2_cache == __f2 IN
  LET (*@type: (() => Set(a213)); *) __d1 == DOMAIN __f1_cache IN
  LET (*@type: (() => Set(a213)); *) __d2 == DOMAIN __f2_cache IN
  [
    __x \in __d1 \union __d2 |->
      IF __x \in __d1 THEN (__f1_cache)[__x] ELSE (__f2_cache)[__x]
  ]

(*
  @type: ((Str, a209) => a209);
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
  @type: ((Int) => a200);
*)
TLCGet(__i) ==
  LET (*@type: (() => Set(a202)); *) __Empty == {} IN
  CHOOSE __x \in __Empty: TRUE

(*
  @type: ((Int, a197) => Bool);
*)
TLCSet(__i, __v) == TRUE

(*
  @type: ((Set(a187)) => Set((a187 -> a187)));
*)
Permutations(__S) ==
  { __f \in [__S -> __S]: \A __w \in __S: \E __v \in __S: __f[__v] = __w }

(*
  @type: ((Set(a184)) => a184);
*)
RandomElement(__s) == CHOOSE __x \in __s: TRUE

(*
  @type: (() => a178);
*)
Any ==
  LET (*@type: (() => Set(a180)); *) __Empty == {} IN
  CHOOSE __x \in __Empty: TRUE

(*
  @type: ((a176) => Str);
*)
ToString(__v) == ""

(*
  @type: ((a174) => a174);
*)
TLCEval(__v) == __v

(*
  @type: ((Seq(a127), ((a127, a127) => Bool)) => (Int -> a127));
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
  @type: (() => <<(NODE -> Bool), (NODE -> Bool), (NODE -> Bool), (NODE -> Bool), Bool>>);
*)
vars == <<lock_msg, grant_msg, unlock_msg, holds_lock, server_holds_lock>>

(*
  @type: ((NODE) => Bool);
*)
SendLock(n) ==
  lock_msg' = [ lock_msg EXCEPT ![n] = TRUE ]
    /\ UNCHANGED (<<unlock_msg, grant_msg, holds_lock, server_holds_lock>>)

(*
  @type: ((NODE) => Bool);
*)
RecvLock(n) ==
  server_holds_lock
    /\ lock_msg[n]
    /\ server_holds_lock' = FALSE
    /\ lock_msg' = [ k \in Node |-> lock_msg[k] /\ k /= n ]
    /\ grant_msg' = [ grant_msg EXCEPT ![n] = TRUE ]
    /\ UNCHANGED (<<unlock_msg, holds_lock>>)

(*
  @type: ((NODE) => Bool);
*)
RecvGrant(n) ==
  grant_msg[n]
    /\ grant_msg' = [ k \in Node |-> grant_msg[k] /\ k /= n ]
    /\ holds_lock' = [ holds_lock EXCEPT ![n] = TRUE ]
    /\ UNCHANGED (<<lock_msg, unlock_msg, server_holds_lock>>)

(*
  @type: ((NODE) => Bool);
*)
Unlock(n) ==
  holds_lock[n]
    /\ holds_lock' = [ k \in Node |-> holds_lock[k] /\ k /= n ]
    /\ unlock_msg' = [ unlock_msg EXCEPT ![n] = TRUE ]
    /\ UNCHANGED (<<lock_msg, grant_msg, server_holds_lock>>)

(*
  @type: ((NODE) => Bool);
*)
RecvUnlock(n) ==
  unlock_msg[n]
    /\ unlock_msg' = [ k \in Node |-> unlock_msg[k] /\ k /= n ]
    /\ server_holds_lock' = TRUE
    /\ UNCHANGED (<<lock_msg, grant_msg, holds_lock>>)

(*
  @type: (() => Bool);
*)
Init ==
  lock_msg = [ n \in Node |-> FALSE ]
    /\ unlock_msg = [ n \in Node |-> FALSE ]
    /\ grant_msg = [ n \in Node |-> FALSE ]
    /\ holds_lock = [ n \in Node |-> FALSE ]
    /\ server_holds_lock = TRUE

(*
  @type: (() => Bool);
*)
TypeOK ==
  lock_msg \in [Node -> BOOLEAN]
    /\ grant_msg \in [Node -> BOOLEAN]
    /\ unlock_msg \in [Node -> BOOLEAN]
    /\ holds_lock \in [Node -> BOOLEAN]
    /\ server_holds_lock \in BOOLEAN

(*
  @type: (() => Bool);
*)
Mutex == \A x \in Node: \A y \in Node: holds_lock[x] /\ holds_lock[y] => x = y

(*
  @type: (() => Bool);
*)
InitializeNode == Node = { "n1_OF_NODE", "n2_OF_NODE", "n3_OF_NODE" }

(*
  @type: (() => Bool);
*)
Next ==
  (\E n \in Node: SendLock(n))
    \/ (\E n \in Node: RecvLock(n))
    \/ (\E n \in Node: RecvGrant(n))
    \/ (\E n \in Node: Unlock(n))
    \/ (\E n \in Node: RecvUnlock(n))

(*
  @type: (() => Bool);
*)
NextUnchanged == UNCHANGED vars

(*
  @type: (() => Bool);
*)
P == Mutex /\ TypeOK

================================================================================
