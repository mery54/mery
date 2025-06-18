-------------------------------- MODULE TLAPROOFMAX2-------------------
EXTENDS Naturals, Integers, TLAPS
---------------------------------------------------------------------
CONSTANTS a0,b0
---------------------------------------------------------------------
typeInt(u) == u \in Int
pre(u,v) == u \in Int /\  v \in Int
maximum(u,v) == IF u <v THEN v ELSE u
---------------------------------------------------------------------
(*
--algorithm maximum  {
variables  a=a0,b=b0,r;
{
w1: if (a < b) {
    r := b;}
    else {
    r := a;
    };
    }
    }
*)
\* BEGIN TRANSLATION (chksum(pcal) = "511d800d" /\ chksum(tla) = "67c371db")
CONSTANT defaultInitValue
VARIABLES a, b, r, pc

vars == << a, b, r, pc >>

Init == (* Global variables *)
        /\ a = a0
        /\ b = b0
        /\ r \in Int
        /\ pc = "w1"

w1 == /\ pc = "w1"
      /\ IF a < b
            THEN /\ r' = b
            ELSE /\ r' = a
      /\ pc' = "Done"
      /\ UNCHANGED << a, b >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == w1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

---------------------    
(* Definitions of invariants *)
i0 ==  typeInt(a) /\ typeInt(b) /\ typeInt(r) /\ a=a0 /\ b=b0 
i1 == pc = "Done" => r =maximum(a0,b0)
InductiveInvariant == i1/\i0 
------------------------------------------------------------------------
ASSUME Assumption == pre(a0,b0) 

THEOREM InitProperty == Init => InductiveInvariant
<1> SUFFICES ASSUME Init
PROVE  InductiveInvariant
OBVIOUS
<1>1. a=a0 BY Assumption  DEF Init
<1>2. b=b0 BY Assumption  DEF Init
<1>3.  pre(a0,b0)  BY Assumption  DEF Init,pre
<1>4. r \in Int  BY  DEF Init
<1>5. pc = "w1" BY DEF Init
<1>6. QED
BY  <1>1, <1>2,<1>3, <1>4, <1>5, Assumption   DEF InductiveInvariant,
 i1,i0,w1, typeInt, pre, Init

-------------------------------------------------------
(* Preservation of i1 by w1 *)

stut == UNCHANGED vars

LEMMA  w1po1 ==
ASSUME  InductiveInvariant, w1
  PROVE  i1'
<1>. USE DEF InductiveInvariant, i1,i0,w1, typeInt, pre
<1>1.  a = a0 /\  b = b0 /\ ((a<b) \/ (a >=b))  BY  SMT 
 DEFS InductiveInvariant, i1,i0,w1, typeInt, pre,maximum
<1>a. CASE a <  b
     <2>1.  pc="w1" /\ a<b /\ r'=b /\ pc' = "Done" /\ UNCHANGED << a, b>>
     BY <1>a,  SMT  DEFS InductiveInvariant, i1,i0,w1, typeInt, pre,maximum
     <2>2.  pc' = "Done" => r' =maximum(a0,b0)
     BY <1>a, <2>1,  SMT  DEFS InductiveInvariant, i1,i0,w1, typeInt, pre,maximum
     <2>3. i1'
     BY <2>2,SMT  DEFS InductiveInvariant, i1,i0,w1, typeInt, pre,maximum         
     <2>. QED
     BY <1>a, <2>1,<2>2,<2>3, SMT DEFS InductiveInvariant, i1,i0,w1, typeInt, pre,maximum
<1>b. CASE a  >=  b
     <2>1.  pc="w1" /\ a >= b /\ r'=a /\ pc' = "Done" /\ UNCHANGED << a, b>>
     BY <1>b,  SMT  DEFS InductiveInvariant, i1,i0,w1, typeInt, pre,maximum
     <2>2.  pc' = "Done" => r' =maximum(a0,b0)
     BY <1>b, <2>1,  SMT  DEFS InductiveInvariant, i1,i0,w1, typeInt, pre,maximum
     <2>3. i1'
     BY <1>b,<2>1,<2>2,SMT  DEFS InductiveInvariant, i1,i0,w1, typeInt, pre,maximum         
     <2>. QED
     BY <1>b, <2>1,<2>2,<2>3, SMT DEFS InductiveInvariant, i1,i0,w1, typeInt, pre,maximum
<1>2. QED     
  BY  <1>a, <1>b, SMT DEFS InductiveInvariant, i1,i0,w1, typeInt, pre,maximum

(* Preservation of i1 by Terminating  *)

LEMMA  Terminatingpo1 ==
ASSUME  InductiveInvariant, Terminating
  PROVE  i1'
<1> USE DEF InductiveInvariant, i1,w1, typeInt, pre, vars  
<1>1  pc = "Done" /\ UNCHANGED vars 
     BY  SMT DEF Terminating
<1>2 i1'
     BY  SMT DEF Terminating
<1>3 QED
     BY <1>1, <1>2,SMT

(* Preservation of i1 by  stuttering *)

LEMMA  stutteringpo ==
ASSUME  InductiveInvariant,stut
  PROVE  i1'
<1> USE DEF InductiveInvariant, i1,  stut, typeInt, pre, vars  
<1>1   i1'
     BY  SMT 
<1>2 QED
     BY <1>1,SMT
     
(* Preservation of i1 by Next *)

LEMMA NextP1 ==
ASSUME InductiveInvariant, Next
PROVE i1'

BY  w1po1, Terminatingpo1  DEFS Next,InductiveInvariant, i1,w1, Terminating,  
typeInt, pre, vars,maximum  
--------------------------
(* Preservation of i0 by w1 *)

LEMMA  w1po0 ==
ASSUME  InductiveInvariant, w1
  PROVE  i0'
<1>. USE DEF InductiveInvariant, i1,i0,w1, typeInt, pre
<1>1.  a = a0 /\  b = b0  BY  SMT  DEFS InductiveInvariant, i1,i0,w1, typeInt, pre,maximum
<1>a. CASE a <  b
     <2>1.  pc="w1" /\ a'=a0 /\ b'=b0 /\ pc' = "Done" /\ UNCHANGED << a, b>>
     BY <1>a,  SMT  DEFS InductiveInvariant, i1,i0,w1, typeInt, pre,maximum
     <2>2.   a'=a0 /\ b'=b0 
     BY <1>a, <2>1,  SMT  DEFS InductiveInvariant, i1,i0,w1, typeInt, pre,maximum
     <2>3. i0'
     BY <2>2,SMT  DEFS InductiveInvariant, i1,i0,w1, typeInt, pre,maximum         
     <2>. QED
     BY <1>a, <2>1,<2>2,<2>3, SMT DEFS InductiveInvariant, i1,i0,w1, typeInt, pre,maximum
<1>b. CASE a  >=  b
     <2>1.  pc="w1" /\  a'=a0 /\ b'=b0  /\ pc' = "Done" /\ UNCHANGED << a, b>>
     BY <1>b,  SMT  DEFS InductiveInvariant, i1,i0,w1, typeInt, pre,maximum
     <2>2.   a'=a0 /\ b'=b0 
     BY <1>b, <2>1,  SMT  DEFS InductiveInvariant, i1,i0,w1, typeInt, pre,maximum
     <2>3. i0'
     BY <1>b,<2>1,<2>2,SMT  DEFS InductiveInvariant, i1,i0,w1, typeInt, pre,maximum         
     <2>. QED
     BY <1>b, <2>1,<2>2,<2>3, SMT DEFS InductiveInvariant, i1,i0,w1, typeInt, pre,maximum
<1>2. QED     
  BY  <1>1, <1>a, <1>b,  SMT DEFS InductiveInvariant, i1,i0,w1, typeInt, pre,maximum


LEMMA  Terminatingpo0 ==
ASSUME  InductiveInvariant, Terminating
  PROVE  i0'
<1> USE DEF InductiveInvariant, i0,w1, typeInt, pre, vars  
<1>1  pc = "Done" /\ UNCHANGED vars 
     BY  SMT DEF Terminating
<1>2 i0'
     BY  SMT DEF Terminating
<1>3 QED
     BY <1>1, <1>2,SMT

(* Preservation of w1 by Terminating  *)

LEMMA  stutteringpo0 ==
ASSUME  InductiveInvariant,stut
  PROVE  i0'
<1> USE DEF InductiveInvariant, i0,  stut, typeInt, pre, vars  
<1>1   i0'
     BY  SMT 
<1>2 QED
     BY <1>1,SMT

(* Preservation of i0 by Next *)

LEMMA NextP0 ==
ASSUME InductiveInvariant, Next
PROVE i0'

BY  w1po0, Terminatingpo0  DEFS Next,InductiveInvariant, i1,w1, Terminating,  
typeInt, pre, vars,maximum  
--------------------------

(* Preservation of InductiveInvariant by Next *)

LEMMA NextP ==
ASSUME InductiveInvariant, Next
PROVE InductiveInvariant'

BY   NextP1,NextP0 DEFS Next, InductiveInvariant, i1,i0,
w1, Terminating,  typeInt, pre,vars  

(* Preservation of InductiveInvariant by Next with stuttering  *)

LEMMA NNextInvariant ==
ASSUME InductiveInvariant,  [Next]_vars
PROVE InductiveInvariant'

BY NextP,stutteringpo, stutteringpo0, PTL DEF Next, stut, InductiveInvariant,vars       

(* Preservation of  InductiveInvariant by Next with stuttering *)

THEOREM INV ==  InductiveInvariant /\   [Next]_vars => InductiveInvariant'
BY NNextInvariant DEFS InductiveInvariant, i1,w1, Terminating,  typeInt, pre,vars  

(* The PlusCal algorithm  satisfies  InductiveInvariant  *)
THEOREM Invariance == Spec => [] InductiveInvariant
<1>1 InductiveInvariant /\   [Next]_vars => InductiveInvariant'
  BY INV  DEF InductiveInvariant, i1,w1, Terminating,  typeInt, pre, vars  
<1>2 Init => InductiveInvariant
BY InitProperty   DEF InductiveInvariant, i1,w1, Terminating,  typeInt, pre, vars  
<1>3 Spec => []InductiveInvariant
  BY PTL, InitProperty, NextP, <1>1 DEF Spec,InductiveInvariant, i1,w1, Terminating, 
   typeInt, pre,vars  
<1> QED
  BY PTL, <1>2, <1>3

=========
