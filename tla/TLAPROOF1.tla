-------------------------------- MODULE TLAPROOF1  --------------------------------
EXTENDS Integers, TLAPS
---------------------------------------------
typeInt(u) == u \in Int
Number == Int
L == {"l1","l2"}
---------------------------------------------
CONSTANTS x0,y0,z0
---------------------------------------------
(* precondition *)
pre == 
    /\ x0 \in Int /\ y0 \in Int /\ z0 \in Int
    /\ x0 = 3 /\ y0=z0+x0 /\ z0=2*x0
---------------------------------------------
VARIABLES  x,y,z,pc
---------------------------------------------
Init == pc="l1" /\ x=x0 /\ y =y0 /\ z = z0  /\ pre
Next ==
/\ pc="l1"
/\ pc'="l2"
/\ y'=z+x
/\ z'=z
/\ x'=x

vars == <<x,y,z,pc>>

Spec == Init /\ [][Next]_vars


InductiveInvariant ==
/\ typeInt(x) /\ typeInt(y) /\ typeInt(z) /\ pc \in L
/\ (pc="l1" =>  x=x0 /\ y=y0 /\ z=z0 /\ pre)
/\ (pc="l2" =>  x=3 /\ y = x +6/\ pre)

ASSUME Assumption == pre


THEOREM InitProperty == Init => InductiveInvariant
<1> SUFFICES ASSUME Init
PROVE  InductiveInvariant
OBVIOUS
<1>1. x=x0 BY Assumption  DEF Init
<1>2. y=y0 BY Assumption  DEF Init
<1>3. z=z0 BY Assumption  DEF Init
<1>4. pc="l1" BY Assumption  DEF Init
<1>5. pre  BY Assumption  DEF Init
<1>7. QED
BY <1>1, <1>2, <1>3,<1>4,<1>5 DEF InductiveInvariant

THEOREM NextProperty == InductiveInvariant /\ [Next]_<<x,y,z,pc>> => InductiveInvariant'

THEOREM Correctness == Spec => []InductiveInvariant
<1>1. Init => InductiveInvariant
  BY DEF Init, pre, L, InductiveInvariant, typeInt
<1>2. InductiveInvariant /\ [Next]_vars => InductiveInvariant'
  BY DEF InductiveInvariant, Next, typeInt, pre, vars, L
<1>. QED  BY <1>1, <1>2, PTL  DEF Spec


=============================================================================


