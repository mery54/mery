-------------------------------- MODULE TLAPROOF2sm  --------------------------------
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
    /\ x<y
    /\ z'=z /\ x'=x /\ y'=y
al1l2 ==
    /\ pc="l1"
    /\ pc'="l2"
    /\ z'=y
    /\ x'=x /\ y'=y
al2l5 ==
    /\ pc="l2"
    /\ pc'="l5"
    /\ z'=z /\ x'=x /\ y'=y
al0l3 ==
    /\ pc="l0"
    /\ pc'="l3"
    /\ x \geq y
    /\ z'=z /\ x'=x /\ y'=y
al3l4 ==
    /\ pc="l3"
    /\ pc'="l4"
    /\ z'=x
    /\ x'=x /\ y'=y
  al4l5 ==
    /\ pc="l4"
    /\ pc'="l5"
    /\ z'=z /\ x'=x /\ y'=y
---------------------    
Init == pc="l0" /\ x=x0 /\ y =y0 /\ z = z0
Next == al0l1 \/ al1l2 \/ al2l5  \/ al0l3 \/ al3l4 \/ al4l5 \/ UNCHANGED <<x,y,z,pc>>
----------------------
vars == <<x,y,z,pc>>
Spec == Init /\ [][Next]_vars


InductiveInvariant ==
   /\ typeInt(x) /\ typeInt(y) /\ typeInt(z)
    /\ pc \in locs
    /\ (pc="l0" =>  x=x0 /\ y=y0)
    /\ (pc="l1" => x<y /\ x=x0 /\ y=y0)
    /\ (pc="l2" => x<y /\ x=x0 /\ y=y0 /\ z=y0)
    /\ (pc="l3" => x \geq y /\ x=x0 /\ y=y0)
    /\ (pc="l4" => x \geq y /\ x=x0 /\ y=y0 /\ z=x0)
    /\ (pc="l5" => ( (x0<y0 /\ z=y0) \/ (x0 \geq y0 /\ z=x0)))
    

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
BY <1>1, <1>2, <1>3,<1>4,<1>5 DEF InductiveInvariant,
  (* sm: added *) typeInt, locs, thepre, pre

(* shorter proof *)
THEOREM Init => InductiveInvariant
BY Assumption DEF Init, InductiveInvariant, typeInt, locs, thepre, pre

THEOREM NextProperty == InductiveInvariant /\ [Next]_<<x,y,z,pc>> => InductiveInvariant'

THEOREM Correctness == Spec => []InductiveInvariant
<1>1. Init => InductiveInvariant
\*  BY DEF Init, pre, L, InductiveInvariant, typeInt
  BY Assumption DEF Init, InductiveInvariant, typeInt, locs, thepre, pre
<1>2. InductiveInvariant /\ [Next]_vars => InductiveInvariant'
  BY DEF InductiveInvariant, Next, typeInt, thepre, vars, \* L
         (* added *) locs, al0l1, al1l2, al2l5, al0l3, al3l4, al4l5
<1>. QED  BY <1>1, <1>2, PTL  DEF Spec


=============================================================================


