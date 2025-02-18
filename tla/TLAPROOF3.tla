-------------------------------- MODULE TLAPROOF3  --------------------------------
EXTENDS Naturals, Integers, TLAPS
CONSTANTS x0,y0,z0,un,intmin, intmax
VARIABLES  x,y,z,pc
---------------------------------------------------------------------
typeInt(u) == u \in Int
maxi(u,v) == IF u < v THEN v ELSE u
locs == {"l0","l1","l2","l3","l4","l5"}
D(X) == (X#un) => (intmin \leq X /\ X \leq intmax)
pre(u,v,w) == u \in Nat /\ v \in Nat /\ typeInt(w)
---------------------------------------------------------------------
(* ASSUME x0 \in Nat /\ y0 \in Nat /\ typeInt(z0) *)
(* ASSUME pre(x0,y0,z0) *)
---------------------------------------------------------------------
Number == Int
L == locs
---------------------------------------------------------------------
(* actions  de l'algorithme *)
al0l1 ==
    /\ pc="l0"
    /\ pc'="l1"
    /\ x'=x
    /\ z'=z /\ x'=x /\ y'=y
---------------------    
Init == pc="l0" /\ x=x0 /\ y =y0 /\ z = z0
Next == al0l1  \/ UNCHANGED <<x,y,z,pc>>
----------------------
vars == <<x,y,z,pc>>
Spec == Init /\ [][Next]_vars


InductiveInvariant ==
   /\ typeInt(x) /\ typeInt(y) /\ typeInt(z)
    /\ pc \in locs
    /\ (pc="l0" =>  x=x0 /\ y=y0)
    /\ (pc="l1" =>  x=x0 /\ y=y0)

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
<1>6. QED
BY <1>1, <1>2, <1>3,<1>4,<1>5 DEF InductiveInvariant

THEOREM NextProperty == InductiveInvariant /\ [Next]_<<x,y,z,pc>> => InductiveInvariant'

THEOREM Correctness == Spec => []InductiveInvariant
<1>1. Init => InductiveInvariant
  BY DEF Init, pre, L, InductiveInvariant, typeInt
<1>2. InductiveInvariant /\ [Next]_vars => InductiveInvariant'
+1  BY DEF InductiveInvariant, Next, typeInt, thepre, vars, locs, al0l1
<1>. QED  BY <1>1, <1>2, PTL  DEF Spec


=============================================================================


