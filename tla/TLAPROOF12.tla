--------- MODULE TLAPROOF12--------
EXTENDS Integers,TLC,TLAPS
--------------------------------------------------------------
CONSTANTS x0,y0,z0
--------------------------------------------------------------
pre == x0=10 /\ z0=2*x0 /\ y0=z0+x0
L == {"l1","l2"}

typeInt(u) == u \in Int



ASSUME pre
(*  *)
(*
--algorithm  test  {
variables x=x0,z=z0,y=y0;
{
l1: y:=z+x;
}
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "66c6fc76" /\ chksum(tla) = "678ca025")
VARIABLES x, z, y, pc

vars == << x, z, y, pc >>

Init == (* Global variables *)
        /\ x = x0
        /\ z = z0
        /\ y = y0
        /\ pc = "l1"

l1 == /\ pc = "l1"
      /\ y' = z+x
      /\ pc' = "Done"
      /\ UNCHANGED << x, z >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == l1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 


\* ASSUME pre


MAX == 32767  (* 16 bits *)
D == -32768..32767
(*  x \leq 32760 *)

DD(X) == (X \in D)

InductiveInvariant ==
    /\ pc \in {"l1","Done"}
    /\ x \in Int /\ y \in Int /\ z \in Int
    /\ pc="l1" =>  x=10 /\  z=2*x /\ y=z+x
    /\ pc="Done" =>   x=10 /\ y=x+2*10

Inv == InductiveInvariant
Safety_Partial_Correctness == pc="Done" =>   x=10 /\ y=x+2*10

Safety_rte ==  DD(x)  /\ DD(y) /\  DD(z) 

check == Inv /\ Safety_Partial_Correctness /\ Safety_rte 

prop == [] (x=x0)
thepre == pre
------------------------------------


ASSUME Assumption == pre

THEOREM InitProperty == Init => InductiveInvariant
<1> SUFFICES ASSUME Init
PROVE  InductiveInvariant
OBVIOUS
<1>1. x=x0 BY Assumption  DEF Init
<1>2. y=y0 BY Assumption  DEF Init
<1>3. z=z0 BY Assumption  DEF Init
<1>4. pc="l1"  BY Assumption  DEF Init
<1>. QED
BY <1>1, <1>2, <1>3, <1>4   DEF InductiveInvariant,typeInt, pre

THEOREM Init => InductiveInvariant
BY Assumption DEF Init, InductiveInvariant, typeInt, thepre, pre

LEMMA truc ==
ASSUME  InductiveInvariant, l1
  PROVE  InductiveInvariant'
BY DEFS InductiveInvariant, l1,typeInt




THEOREM NextProperty == 
ASSUME InductiveInvariant, [Next]_<<x>>
PROVE InductiveInvariant'

<1> SUFFICES ASSUME InductiveInvariant /\ [Next]_<<x>>
PROVE  InductiveInvariant'
OBVIOUS
<1>1. x'\in 0..x0 /\ typeInt(x')  => InductiveInvariant'  
BY  PTL  DEF InductiveInvariant
<1>2. 
ASSUME InductiveInvariant, l1
PROVE  InductiveInvariant'
BY Zenon, SMT, PTL DEF InductiveInvariant,l1,typeInt
<1>. QED
BY <1>1,<1>2,Zenon, SMT,PTL  DEF InductiveInvariant,typeInt, thepre, pre




THEOREM Correctness == Spec => []InductiveInvariant
<1>1. Init => InductiveInvariant
  BY Assumption DEF Init, InductiveInvariant, typeInt, thepre, pre
<1>2. InductiveInvariant /\ [Next]_vars => InductiveInvariant'
  BY PTL DEF InductiveInvariant, Next, typeInt, thepre, vars, 
         l1
<1>. QED  BY <1>1, <1>2, PTL  DEF Spec


=========
