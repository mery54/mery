------------- MODULE TLAPROOF6 --------------------------
EXTENDS Naturals, Integers,TLC,TLAPS
---------------------------------------------------------
CONSTANTS x0, intmin, intmax
---------------------------------------------------------
VARIABLES  x,pc
---------------------------------------------------------
pre(u) == u \in Nat
typeInt(u) == u \in Int 
D(X) == intmin \leq X /\ X \leq intmax
labs == {"l0","l1","l2","l3"}
thepre == pre(x0)
---------------------------------------------------------
ASSUME pre(x0)
---------------------------------------------------------
al0l1 ==
    /\ pc="l0"
    /\ 0<x
    /\ pc'="l1"
    /\ x' = x
al1l2 ==
    /\ pc="l1"
    /\ pc'="l2"
    /\ x'=x-1 
  
al2l3 ==
    /\ pc="l2"
    /\ 0 \geq x
    /\ pc'="l3"
    /\ x'=x 
    
al2l1 ==
    /\ pc="l2"
    /\ pc'="l1"
    /\ 0  <  x
    /\ x'=x 
al0l3 ==
    /\ pc="l0"
    /\ 0 \geq x
    /\ pc'="l3"
    /\  x'=x 
---------------------------------------------------------

Init == pc="l0" /\ x=x0
Next == 
    \/ al0l1 \/ al1l2 \/ al2l3  
    \/ al0l3 \/ al2l1 
    \/ UNCHANGED <<x,pc>>
vars == <<pc,x>>
Spec == Init/\  [] [Next]_vars
---------------------------------------------------------
InductiveInvariant ==  
    /\ typeInt(x)
    /\ pc \in {"l0","l1","l2","l3"} 
    /\ pc="l0" =>  x=x0 /\ x0 \in Nat
    /\ pc="l1" => 0 < x /\ x \leq x0 /\ x0 \in Nat
    /\ pc="l2" => 0 \leq x  /\  x  < x0 /\ x0 \in Nat
    /\ pc="l3" => x = 0


saferte ==   D(x)

safepc ==  pc="l3" => x=0

Safe == safepc /\ saferte /\ InductiveInvariant
---------------------------------------------------------
ASSUME Assumption == thepre

THEOREM InitProperty == Init => InductiveInvariant
<1> SUFFICES ASSUME Init
PROVE  InductiveInvariant
OBVIOUS
<1>1. x=x0 BY Assumption  DEF Init
<1>2. pc="l0" BY Assumption  DEF Init
<1>3.  thepre  BY Assumption  DEF Init
<1>. QED BY <1>1, <1>2, <1>3   DEF InductiveInvariant,typeInt, labs, thepre,pre

THEOREM Init => InductiveInvariant
BY Assumption DEF Init, InductiveInvariant, typeInt, labs, thepre, pre

THEOREM NextProperty == InductiveInvariant /\ [Next]_<<x,pc>> => InductiveInvariant'
 BY DEF InductiveInvariant, Next, typeInt, thepre,vars,labs,al0l1,al1l2,al2l3,al2l1,al0l3
 
THEOREM Correctness == Spec => [] InductiveInvariant
<1>1. Init => InductiveInvariant
  BY Assumption DEF Init, InductiveInvariant, typeInt, labs, thepre, pre
<1>2. InductiveInvariant /\ [Next]_vars => InductiveInvariant'
  BY DEF InductiveInvariant, Next, typeInt, thepre,vars,labs,al0l1,al1l2,al2l3,al2l1,al0l3
<1>. QED  BY <1>1, <1>2, PTL  DEF Spec

=========


