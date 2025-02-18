-------------------------------- MODULE TLAPROOFMAX  -------------------
EXTENDS Naturals, Integers, TLAPS
---------------------------------------------------------------------
CONSTANTS a,b
---------------------------------------------------------------------
VARIABLES  i,j,sup,ok
---------------------------------------------------------------------
typeInt(u) == u \in Int
B == {0,1}
typeB(u) == u \in B
pre(u,v) == u \in Int /\ v \in Int
---------------------------------------------------------------------

evt1  ==
    /\ ok=0
    /\ i<j
    /\ ok' = 1
    /\  sup'=j
    /\ i' = i /\ j' = j

evt2  ==
    /\ ok=0
    /\ i<j
    /\ ok' = 1
    /\  sup'=j
    /\ i' = i /\ j' = j
    
---------------------    

Init ==  i=a /\ j =b /\ sup \in Int  /\ ok=0 
Next == evt1 \/ evt2  \/ UNCHANGED <<i,j,sup,ok>>
vars == <<i,j,sup,ok>>
Spec == Init /\ [] [Next]_vars
------------------------------------------------------------------------

i1 == typeInt(i) /\ typeInt(j) /\ typeInt(sup) /\ typeB(ok)
i2 ==   i=a /\ j=b
i3 ==  ( (ok=1) => a <= sup /\ b <= sup /\ sup \in {a,b})

InductiveInvariant == i1 /\ i2 /\ i3
------------------------------------------------------------------------

ASSUME Assumption == pre(a,b) 

THEOREM InitProperty == Init => InductiveInvariant
<1> SUFFICES ASSUME Init
PROVE  InductiveInvariant
OBVIOUS
<1>1. i=a BY Assumption  DEF Init
<1>2. j=b BY Assumption  DEF Init
<1>3. sup \in Int BY Assumption  DEF Init
<1>4. ok=0 BY Assumption  DEF Init
<1>5.  pre(a,b)  BY Assumption  DEF Init
<1>6. QED
BY <1>1, <1>2, <1>3,<1>4,<1>5 DEF InductiveInvariant, i1,i2,i3,Init,
   typeInt,B, typeB, pre

THEOREM Init => InductiveInvariant
BY Assumption DEF Init, InductiveInvariant, i1,i2,i3, typeInt,B, typeB, pre



LEMMA evt1po1 ==
ASSUME  InductiveInvariant, evt1
  PROVE  i1'
BY PTL DEFS InductiveInvariant, evt1,typeInt


LEMMA evt1po2 ==
ASSUME  InductiveInvariant, evt1
  PROVE  i2'
BY PTL DEFS InductiveInvariant, evt1,typeInt


LEMMA evt1po3 ==
ASSUME  InductiveInvariant, evt1
  PROVE  i3'
BY PTL DEFS InductiveInvariant, evt1,typeInt

LEMMA evt2po1 ==
ASSUME  InductiveInvariant, evt2
  PROVE  i1'
BY PTL DEFS InductiveInvariant, evt2,typeInt


LEMMA evt2po2 ==
ASSUME  InductiveInvariant, evt2
  PROVE  i2'
BY PTL DEFS InductiveInvariant, evt2,typeInt


LEMMA evt2po3 ==
ASSUME  InductiveInvariant, evt2
  PROVE  i3'
BY PTL DEFS InductiveInvariant, evt2,typeInt


LEMMA evt1po ==
ASSUME  InductiveInvariant, evt1
  PROVE  InductiveInvariant'
BY PTL DEFS InductiveInvariant, evt1,typeInt


LEMMA evt2po ==
ASSUME  InductiveInvariant, evt2
  PROVE  InductiveInvariant'
BY PTL DEFS InductiveInvariant, evt2,typeInt

LEMMA NextP ==
ASSUME InductiveInvariant, Next
PROVE InductiveInvariant'

BY evt1po,evt2po, PTL DEF Next, InductiveInvariant


stut == UNCHANGED <<i,j,sup,ok>>

LEMMA stutteringpo ==
ASSUME  InductiveInvariant, stut
  PROVE  InductiveInvariant'
BY PTL DEFS InductiveInvariant,  stut,typeInt




LEMMA NNextInvariant ==
ASSUME InductiveInvariant,  [Next]_vars
PROVE InductiveInvariant'

BY NextP,stutteringpo, PTL DEF Next, stut, InductiveInvariant,vars       


THEOREM INV ==  InductiveInvariant /\   [Next]_vars => InductiveInvariant'
BY NNextInvariant DEFS InductiveInvariant,i1,i2,i3,typeInt,B,typeB


THEOREM Invariance == Spec => [] InductiveInvariant
<1>1 InductiveInvariant /\   [Next]_vars => InductiveInvariant'
  BY INV  DEF InductiveInvariant,i1,i2,i3,typeInt,B,typeB
<1>2 Init => InductiveInvariant
BY InitProperty   DEF InductiveInvariant,i1,i2,i3,typeInt,B,typeB
<1>3 Spec => []InductiveInvariant
  BY PTL, InitProperty, NextP, <1>1 DEF Spec,InductiveInvariant,i1,i2,i3,typeInt,B,typeB
<1> QED
  BY PTL, <1>2, <1>3

THEOREM Correctness == Spec => [] i3
<1>1 InductiveInvariant /\   [Next]_vars => InductiveInvariant'
  BY INV  DEF InductiveInvariant,i1,i2,i3,typeInt,B,typeB
<1>2 Init => InductiveInvariant
BY InitProperty   DEF InductiveInvariant,i1,i2,i3,typeInt,B,typeB
<1>3 Spec => []InductiveInvariant
  BY PTL, InitProperty, NextP, <1>1 DEF Spec,InductiveInvariant,i1,i2,i3,typeInt,B,typeB
  <1>4 InductiveInvariant => i3
  BY PTL, InitProperty, NextP, <1>1 DEF Spec,InductiveInvariant,i1,i2,i3,typeInt,B,typeB
<1> QED
  BY PTL, <1>2, <1>3, <1>4


=========



