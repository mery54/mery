-------------------------------- MODULE TLAPROOF8  --------------------------------
EXTENDS Naturals, Integers, TLAPS
CONSTANTS x0
VARIABLES  x
---------------------------------------------------------------------
typeInt(u) == u \in Int
pre(u) == u \in Nat
---------------------------------------------------------------------
(* actions *)
a ==
    /\ x>0
    /\ x'=x-1
---------------------    
Init == x=x0 
Next == a \/ UNCHANGED <<x>>
----------------------
vars == <<x>>
Spec == Init /\ [][Next]_vars


InductiveInvariant ==
   /\ typeInt(x) 
   /\ x \in 0..x0


thepre == pre(x0)

ASSUME Assumption == thepre

THEOREM InitProperty == Init => InductiveInvariant
<1> SUFFICES ASSUME Init
PROVE  InductiveInvariant
OBVIOUS
<1>1. x=x0 BY Assumption  DEF Init
<1>2. thepre  BY Assumption  DEF Init
<1>. QED
BY <1>1, <1>2   DEF InductiveInvariant,typeInt, thepre, pre

THEOREM Init => InductiveInvariant
BY Assumption DEF Init, InductiveInvariant, typeInt, thepre, pre

LEMMA truc ==
ASSUME  InductiveInvariant, a
  PROVE  InductiveInvariant'
BY DEFS InductiveInvariant, a,typeInt



THEOREM NextProperty == 
ASSUME InductiveInvariant, [Next]_<<x>>
PROVE InductiveInvariant'

<1> SUFFICES ASSUME InductiveInvariant /\ [Next]_<<x>>
PROVE  InductiveInvariant'
OBVIOUS
<1>1. x'\in 0..x0 /\ typeInt(x')  => InductiveInvariant'  
BY  PTL  DEF InductiveInvariant
<1>2. 
ASSUME InductiveInvariant, a 
PROVE  x'\in 0..x0 /\ typeInt(x') 
BY Zenon, SMT, PTL DEF InductiveInvariant,a,typeInt
<1>. QED
BY <1>1,<1>2,Zenon, SMT,PTL  DEF InductiveInvariant,typeInt, thepre, pre




THEOREM Correctness == Spec => []InductiveInvariant
<1>1. Init => InductiveInvariant
  BY Assumption DEF Init, InductiveInvariant, typeInt, thepre, pre
<1>2. InductiveInvariant /\ [Next]_vars => InductiveInvariant'
  BY PTL DEF InductiveInvariant, Next, typeInt, thepre, vars, 
         a
<1>. QED  BY <1>1, <1>2, PTL  DEF Spec


=============================================================================


