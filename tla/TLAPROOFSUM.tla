-------------------------------- MODULE TLAPROOFADD  -------------------
EXTENDS Naturals, Integers, TLAPS
---------------------------------------------------------------------
CONSTANTS x0,y0
---------------------------------------------------------------------
VARIABLES  x,y,z,ok
---------------------------------------------------------------------
typeInt(u) == u \in Int
B == {0,1}
typeB(u) == u \in B
pre(u,v) == u \in Nat /\ v \in Nat
---------------------------------------------------------------------


(*
--algorithm oddeven {
variables  rs=0,re=0,input=n,cur=0,ce=0,cs=0;
{

w:while (i # n) {
      if (cur % 2 # 0) {
        cs := cs+cur+1;
        ce := ce+cur+1;
        cur := cur+1;	}
	else
	{
        cs := cs+cur+1;
        ce :=ce;
        cur := cur+1;
	};
	};
	}
	}
*)


------------------------------------------------------------------------

i1 == typeInt(x) /\ typeInt(y) /\ typeInt(z) /\ typeB(ok)
i2 ==   x \in 0..x0
i3 == y \in 0..y0
i4 == z = (x0 - x) + (y - y0)
i5 == ( (ok=1) =>  (z = x0+y0))
InductiveInvariant == i1 /\ i2 /\ i3 /\ i4 /\ i5
------------------------------------------------------------------------

ASSUME Assumption == pre(x0,y0) 

THEOREM InitProperty == Init => InductiveInvariant
<1> SUFFICES ASSUME Init
PROVE  InductiveInvariant
OBVIOUS
<1>1. x=x0 BY Assumption  DEF Init
<1>2. y=y0 BY Assumption  DEF Init
<1>3. z=0 BY Assumption  DEF Init
<1>4. ok=0 BY Assumption  DEF Init
<1>5.  pre(x0,y0)  BY Assumption  DEF Init
<1>6. QED
BY <1>1, <1>2, <1>3,<1>4,<1>5 DEF InductiveInvariant, i1,i2,i3,i4,i5,Init,
   typeInt,B, typeB, pre

THEOREM Init => InductiveInvariant
BY Assumption DEF Init, InductiveInvariant, i1,i2,i3,i4,i5, typeInt,B, typeB, pre



LEMMA evt1po1 ==
ASSUME  InductiveInvariant, evt1
  PROVE  i1'
BY  DEFS InductiveInvariant, evt1,typeInt,typeB


LEMMA evt1po2 ==
ASSUME  InductiveInvariant, evt1
  PROVE  i2'
BY PTL DEFS InductiveInvariant, evt1,typeInt


LEMMA evt1po3 ==
ASSUME  InductiveInvariant, evt1
  PROVE  i3'
BY PTL DEFS InductiveInvariant, evt1,typeInt


LEMMA evt1po4 ==
ASSUME  InductiveInvariant, evt1
  PROVE  i4'
BY PTL DEFS InductiveInvariant, evt1,typeInt


LEMMA evt1po5 ==
ASSUME  InductiveInvariant, evt1
  PROVE  i5'
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


LEMMA evt2po4 ==
ASSUME  InductiveInvariant, evt2
  PROVE  i4'
BY PTL DEFS InductiveInvariant, evt2,typeInt


LEMMA evt2po5 ==
ASSUME  InductiveInvariant, evt2
  PROVE  i5'
BY PTL DEFS InductiveInvariant, evt2,typeInt



LEMMA evt3po1 ==
ASSUME  InductiveInvariant, evt3
  PROVE  i1'
BY PTL DEFS InductiveInvariant, evt3,typeInt


LEMMA evt3po2 ==
ASSUME  InductiveInvariant, evt3
  PROVE  i2'
BY PTL DEFS InductiveInvariant, evt3,typeInt


LEMMA evt3po3 ==
ASSUME  InductiveInvariant, evt3
  PROVE  i3'
BY PTL DEFS InductiveInvariant, evt3,typeInt


LEMMA evt3po4 ==
ASSUME  InductiveInvariant, evt3
  PROVE  i4'
BY PTL DEFS InductiveInvariant, evt3,typeInt


LEMMA evt3po5 ==
ASSUME  InductiveInvariant, evt3
  PROVE  i5'
BY PTL DEFS InductiveInvariant, evt3,typeInt



LEMMA evt1po ==
ASSUME  InductiveInvariant, evt1
  PROVE  InductiveInvariant'
BY PTL DEFS InductiveInvariant, evt1,typeInt


LEMMA evt2po ==
ASSUME  InductiveInvariant, evt2
  PROVE  InductiveInvariant'
BY PTL DEFS InductiveInvariant, evt2,typeInt


LEMMA evt3po ==
ASSUME  InductiveInvariant, evt3
  PROVE  InductiveInvariant'
BY PTL DEFS InductiveInvariant, evt3,typeInt


LEMMA NextP ==
ASSUME InductiveInvariant, Next
PROVE InductiveInvariant'

BY evt1po,evt2po,evt3po, PTL DEF Next, InductiveInvariant


stut == UNCHANGED <<x,y,z,ok>>

LEMMA stutteringpo ==
ASSUME  InductiveInvariant, stut
  PROVE  InductiveInvariant'
BY PTL DEFS InductiveInvariant,  stut,typeInt




LEMMA NNextInvariant ==
ASSUME InductiveInvariant,  [Next]_vars
PROVE InductiveInvariant'

BY NextP,stutteringpo, PTL DEF Next, stut, InductiveInvariant,vars       


THEOREM INV ==  InductiveInvariant /\   [Next]_vars => InductiveInvariant'
BY NNextInvariant DEFS InductiveInvariant,i1,i2,i3,i4,i5,typeInt,B,typeB


THEOREM Invariance == Spec => [] InductiveInvariant
<1>1 InductiveInvariant /\   [Next]_vars => InductiveInvariant'
  BY INV  DEF InductiveInvariant,i1,i2,i3,i4,i5,typeInt,B,typeB
<1>2 Init => InductiveInvariant
BY InitProperty   DEF InductiveInvariant,i1,i2,i3,i4,i5,typeInt,B,typeB
<1>3 Spec => []InductiveInvariant
  BY PTL, InitProperty, NextP, <1>1 DEF Spec,InductiveInvariant,i1,i2,i3,i4,i5,typeInt,B,typeB
<1> QED
  BY PTL, <1>2, <1>3

THEOREM Correctness == Spec => [] i5
<1>1 InductiveInvariant /\   [Next]_vars => InductiveInvariant'
  BY INV  DEF InductiveInvariant,i1,i2,i3,i4,i5,typeInt,B,typeB
<1>2 Init => InductiveInvariant
BY InitProperty   DEF InductiveInvariant,i1,i2,i3,i4,i5,typeInt,B,typeB
<1>3 Spec => []InductiveInvariant
  BY PTL, InitProperty, NextP, <1>1 DEF Spec,InductiveInvariant,i1,i2,i3,i4,i5,typeInt,B,typeB
  <1>4 InductiveInvariant => i5
  BY PTL, InitProperty, NextP, <1>1 DEF Spec,InductiveInvariant,i1,i2,i3,i4,i5,typeInt,B,typeB
<1> QED
  BY PTL, <1>2, <1>3, <1>4


=========



