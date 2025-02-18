------------- MODULE TLAPROOF5 --------------------------------
EXTENDS Naturals, Integers,TLC, TLAPS
CONSTANTS x0,y0,z0
VARIABLES  x,y,z,pc
-------------------------------------------------------------------------------
(* Auxiliary definitions *)
typeInt(u) == u \in Int
pre(u,v,w) == /\ u \in Int /\ v \in Int /\ w \in Int
       /\  u=3 /\ v=w+u /\ w=2*u
       L == {"l1","l2"}
------------------------------------------------------------------------------
(* Interpretation: we assume that the precondition can hold and we have to find possible values for x0,y0, z0 to validate or not *)
ASSUME   pre(x0,y0,z0)
---------------------------------------------------------------------
(* Action for transition of the algorithm *)
al1l2 ==
    /\ pc="l1"
    /\ pc'="l2"
    /\ y'=z+x
    /\ z'=z /\ x'=x
---------------------------------------------------------------
(* Computations *)
vars ==  <<x,y,z,pc>>
Next == al1l2  \/ UNCHANGED vars
Init == pc="l0" /\ x=x0 /\ y =y0 /\ z = z0  /\ pre(x0,y0,z0)
----------------------
(* Checking the annotation by checking the invariant i derived from the annotation *)
i ==
    /\ typeInt(x) /\ typeInt(y) /\ typeInt(z)
    /\ pc="l1" =>  x=x0 /\ y=y0 /\ z=z0 /\ pre(x0,y0,z0)
    /\ pc="l2" =>  x=3 /\ y = x +6 /\ pre(x0,y0,z0)

Safe ==  i
Spec == Init /\ [][Next]_vars
------------------------------------------------------------------------------

InductiveInvariant ==
    /\ typeInt(x) /\ typeInt(y) /\ typeInt(z)
    /\ pc="l1" =>  x=x0 /\ y=y0 /\ z=z0 /\ pre(x0,y0,z0) 
    /\ pc="l2" =>  x=3 /\ y = x +6 /\ pre(x0,y0,z0)

thepre == pre(x0,y0,z0)

ASSUME Assumption == thepre


THEOREM InitProperty == Init => InductiveInvariant
<1> SUFFICES ASSUME Init
PROVE  InductiveInvariant
OBVIOUS
<1>1. x=x0 BY Assumption  DEF Init
<1>2. y=y0 BY Assumption  DEF Init
<1>3. z=z0 BY Assumption  DEF Init
<1>4. pc="l0" BY Assumption  DEF Init
<1>5.  thepre  BY Assumption  DEF Init
<1>7. QED
BY <1>1, <1>2, <1>3,<1>4,<1>5 DEF InductiveInvariant,
  typeInt, L, thepre, pre


THEOREM Init => InductiveInvariant
BY Assumption DEF Init, InductiveInvariant, typeInt, L, thepre, pre

THEOREM NextProperty == InductiveInvariant /\ [Next]_<<x,y,z,pc>> => InductiveInvariant'
 BY DEF InductiveInvariant, Next, typeInt, thepre, pre,  vars,  L,  al1l2
 
THEOREM Correctness == Spec => []InductiveInvariant
<1>1. Init => InductiveInvariant
\*  BY DEF Init, thepre, pre, L, InductiveInvariant, typeInt
  BY Assumption DEF Init, InductiveInvariant, typeInt, L, thepre, pre
<1>2. InductiveInvariant /\ [Next]_vars => InductiveInvariant'
  BY DEF InductiveInvariant, Next, typeInt, thepre, pre,  vars,  L,  al1l2
<1>. QED  BY <1>1, <1>2, PTL  DEF Spec



=========