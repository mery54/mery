-------------------------------- MODULE TLAPROOFEX10bis --------------------------------

EXTENDS Naturals, Integers,TLC,TLAPS
CONSTANTS x0,y0
VARIABLES  x,y,pc
------------------------------------------------------------------------------
(* Interpretation: w assume that the precondition can hold and we have to find possible values for x0,y0, z0 to validate or not *)
ASSUME /\ x0 \in Int /\ y0 \in Int 
       /\  x0=2^4 /\ y0=2 /\ x0*y0=2^5
-------------------------------------------------------------------------------
(* Auxiliary definitions *)
typeInt(u) == u \in Int
pre == /\ x0 \in Int /\ y0 \in Int 
       /\  x0=2^4 /\ y0=2 /\ x0*y0=2^5
vars == <<x,y,pc>>
L == { "l1", "l2"}
---------------------------------------------------------------------
(* Action for transitioon of the algorithm *)
al1l2 ==
    /\ pc="l1"
    /\ pc'="l2"
    /\ x'=y+x+2^x
    /\ y'=y

Skip == UNCHANGED vars
---------------------------------------------------------------
(* Computations *)
Next == al1l2  \/ Skip
Init == pc="l1" /\ x=x0 /\ y =y0  /\ pre
Spec == Init /\ [Next]_vars
----------------------
(* Checking the annotation by checking the invariant i derived from the annotation *)
i ==
    /\ typeInt(x) /\ typeInt(y) 
    /\ pc="l1" =>  x=x0 /\ y=y0 /\ pre
    /\ pc="l2" =>  x=2^10 /\ y = 2


InductiveInvariant == i

ASSUME Assumption == pre

THEOREM InitProperty == Init => InductiveInvariant
<1> SUFFICES ASSUME Init
PROVE  InductiveInvariant
OBVIOUS
<1>1. x=x0 BY Assumption  DEF Init
<1>2.  pre  BY Assumption  DEF Init
<1>3. y=y0 BY  DEF Init
<1>4. pc = "l1" BY DEF Init
<1>5. QED
BY  <1>1, <1>2,<1>3, <1>4  DEF InductiveInvariant, i, typeInt, pre,L





LEMMA al1l2po ==
ASSUME  InductiveInvariant, al1l2
  PROVE  i'
<1> USE DEF InductiveInvariant, i,al1l2, typeInt, pre,L
<1>1 typeInt(x') /\ typeInt(y') /\ pc' \in  L
BY SMT  DEFS InductiveInvariant, i, typeInt, pre,L
<1>2 i'
     BY <1>1, SMT
<1>3 QED
     BY <1>1, <1>2, SMT



LEMMA Skippo ==
ASSUME  InductiveInvariant, Skip
  PROVE  i'

<1> USE DEF InductiveInvariant, i,typeInt, pre,L,Skip

<1>1 pc  \in L
     BY  DEFS  InductiveInvariant, i,typeInt, pre,L,Skip
<1>2 (pc="l1") \/ (pc="l2")
     BY <1>1   DEFS  InductiveInvariant, i,typeInt, pre,L,Skip

<1>a CASE pc="l1"
     <2>1  pc' = "l1" /\ UNCHANGED vars
     BY <1>a, SMT DEFS  InductiveInvariant, i,typeInt, pre,L,Skip,vars
     <2>2 typeInt(x') /\ typeInt(y') /\  pc' \in  L
     BY <1>a,<2>1   DEFS  InductiveInvariant, i,typeInt, pre,L,Skip,vars  
     <2>3  pc'="l1" =>  x'=x0 /\ y'=y0 /\ pre
     BY <1>a,<2>1   DEFS  InductiveInvariant, i,typeInt, pre,L,Skip,vars
     <2>4 pc'="l2" =>   x'=2^10 /\ y' = 2
     BY <1>a,<2>1   DEFS  InductiveInvariant, i,typeInt, pre,L,Skip,vars  
     <2>5 i'
     BY <1>a,<2>1,<2>2,<2>3,<2>4   DEFS  InductiveInvariant, i,typeInt, pre,L,Skip,vars  
     <2> QED
     BY <1>a, <2>1, <2>2,<2>3,<2>4, <2>5,    SMT  DEFS  InductiveInvariant, i,typeInt, pre,L,Skip,vars  
<1>b CASE pc="l2"
   <2>1  pc' = "l2" /\ UNCHANGED vars
     BY <1>b, SMT DEFS  InductiveInvariant, i,typeInt, pre,L,Skip,vars
     <2>2 typeInt(x') /\ typeInt(y')  /\ pc' \in  L
     BY <1>b,<2>1   DEFS  InductiveInvariant, i,typeInt, pre,L,Skip,vars  
     <2>3   pc'="l1" =>  x'=x0 /\ y'=y0 /\ pre
     BY <1>b,<2>1   DEFS  InductiveInvariant, i,typeInt, pre,L,Skip,vars
     <2>4 pc'="l2" =>   x'=2^10 /\ y' = 2
     BY <1>b,<2>1   DEFS  InductiveInvariant, i,typeInt, pre,L,Skip,vars  
     <2>5 i'
     BY <1>b,<2>1,<2>2,<2>3,<2>4   DEFS  InductiveInvariant, i,typeInt, pre,L,Skip,vars  
     <2> QED
     BY <1>b, <2>1, <2>2,<2>3,<2>4, <2>5,SMT  DEFS  InductiveInvariant, i,typeInt, pre,L,Skip,vars  

<1>3 QED     
  BY <1>2, <1>a, <1>b  DEFS  InductiveInvariant, i,typeInt, pre,L,Skip, vars


LEMMA NextP ==
ASSUME InductiveInvariant, Next
PROVE i'

BY al1l2po, Skippo DEFS Next, InductiveInvariant, i,typeInt, pre,L,Skip, al1l2, vars 



LEMMA NNextInvariant ==
ASSUME InductiveInvariant,  [Next]_vars
PROVE InductiveInvariant'

BY NextP, PTL DEF Next, InductiveInvariant, i,typeInt, pre,L,Skip, al1l2, vars 

THEOREM INV ==  InductiveInvariant /\   [Next]_vars => InductiveInvariant'
BY NNextInvariant DEFS Next, InductiveInvariant, i,typeInt, pre,L,Skip, al1l2, vars 


=======
THEOREM Invariance == Spec => []InductiveInvariant

<1>1. InductiveInvariant /\   [Next]_vars => InductiveInvariant'
  BY INV  DEFS  Next, InductiveInvariant, i,typeInt, pre,L,Skip, al1l2, vars 

<1>2. Init => InductiveInvariant
BY InitProperty  DEFS Init,InductiveInvariant  

<1>3. Spec => []InductiveInvariant
  BY InitProperty, NextP, INV, <1>1,<1>2, PTL DEFS Spec, Next, InductiveInvariant, i,typeInt, pre,L,Skip, al1l2, vars 

<1> QED
  BY InitProperty, NextP, <1>1,<1>2, <1>3,PTL DEFS  Spec, Next, InductiveInvariant, i,typeInt, pre,L,Skip, al1l2, vars 


Safe == i

THEOREM Safety == Spec => [] Safe 

BY  Invariance DEFS Safe


=============================================================================
\* Modification History
\* Last modified Tue Feb 07 11:35:34 CET 2023 by mery
\* Created Wed Sep 09 18:19:08 CEST 2015 by mery
