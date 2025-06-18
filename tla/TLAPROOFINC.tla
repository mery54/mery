-------------------------------- MODULE TLAPROOFINC  -------------------
EXTENDS Naturals, Integers, TLAPS
---------------------------------------------------------------------
CONSTANTS x0
---------------------------------------------------------------------
typeInt(u) == u \in Int
pre(u) == u \in Nat 
---------------------------------------------------------------------

(*
--algorithm inc {
  variables x=x0;
  {
  x:=x+1;
  }
}

*)
\* BEGIN TRANSLATION (chksum(pcal) = "e23deda2" /\ chksum(tla) = "9a71d89e")
VARIABLES x, pc

vars == << x, pc >>

Init == (* Global variables *)
        /\ x = x0
        /\ pc = "Lbl_1"

evt1 == /\ pc = "Lbl_1"
         /\ x' = x+1
         /\ pc' = "Done"

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == evt1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 


---------------------    
i1 == typeInt(x) /\ pc \in {"Lbl_1","Done"}
i2 ==   x \in x0..x0+1
i3 ==  pc= "Done"  => x=x0+1
i4 ==  pc =  "Lbl_1" => x=x0
InductiveInvariant == i1 /\ i2 /\ i3 /\ i4 
------------------------------------------------------------------------

ASSUME Assumption == pre(x0) 

THEOREM InitProperty == Init => InductiveInvariant
<1> SUFFICES ASSUME Init
PROVE  InductiveInvariant
OBVIOUS
<1>1. x=x0 BY Assumption  DEF Init
<1>2.  pre(x0)  BY Assumption  DEF Init
<1>3. QED
BY <1>1, <1>2 DEF InductiveInvariant, i1,i2,i3,i4,Init,typeInt,pre

THEOREM Init => InductiveInvariant
BY Assumption DEF Init, InductiveInvariant, i1,i2,i3,i4,typeInt,pre




LEMMA evt1po1 ==
ASSUME  InductiveInvariant, evt1
PROVE  i1'
BY DEFS InductiveInvariant,evt1,typeInt,pre,vars,i1,i2,i3,i4


LEMMA evt1po2 ==
ASSUME  InductiveInvariant, evt1
PROVE  i2'
BY DEFS InductiveInvariant,evt1,typeInt,pre,vars,i1,i2,i3,i4


LEMMA evt1po3 ==
ASSUME  InductiveInvariant, evt1
PROVE  i3'
BY DEFS InductiveInvariant, i1,i2,i3,i4, evt1,typeInt,pre,vars


LEMMA evt1po4 ==
ASSUME  InductiveInvariant, evt1
PROVE  i4'
BY  DEFS InductiveInvariant, i1,i2,i3,i4, evt1,typeInt,pre,vars




LEMMA evt1po ==
ASSUME  InductiveInvariant, evt1
  PROVE  InductiveInvariant'
BY evt1po1,evt1po2,evt1po3,evt1po4,PTL DEFS InductiveInvariant, 
i1,i2,i3,i4, evt1,typeInt,pre,vars



LEMMA Terminatingpo ==
ASSUME  InductiveInvariant, Terminating
  PROVE  InductiveInvariant'
BY  DEFS InductiveInvariant, i1,i2,i3,i4, Terminating,typeInt,pre,vars



LEMMA NextP ==
ASSUME InductiveInvariant, Next
PROVE InductiveInvariant'

BY evt1po, Terminatingpo , PTL DEF Next, InductiveInvariant, i1,i2,i3,i4,
 evt1,typeInt,pre,vars


stut == UNCHANGED <<x,pc>>

LEMMA stutteringpo ==
ASSUME  InductiveInvariant, stut
  PROVE  InductiveInvariant'
BY  DEFS stut, InductiveInvariant, i1,i2,i3,i4, evt1,typeInt,pre,vars




LEMMA NNextInvariant ==
ASSUME InductiveInvariant,  [Next]_vars
PROVE InductiveInvariant'

BY NextP,stutteringpo, PTL DEF Next, stut, InductiveInvariant, i1,i2,i3,i4, 
stut, typeInt,pre,vars      


THEOREM INV ==  InductiveInvariant /\   [Next]_vars => InductiveInvariant'
BY NNextInvariant DEFS Next, stut, InductiveInvariant, i1,i2,i3,i4, stut, 
typeInt,pre,vars



THEOREM Invariance == Spec => [] InductiveInvariant
<1>1 InductiveInvariant /\   [Next]_vars => InductiveInvariant'
  BY INV  DEF InductiveInvariant,i1,i2,i3,i4,typeInt
<1>2 Init => InductiveInvariant
BY InitProperty   DEF InductiveInvariant,i1,i2,i3,i4,typeInt
<1>3 Spec => []InductiveInvariant
  BY PTL, InitProperty, NextP, <1>1 DEF Spec,InductiveInvariant,i1,i2,i3,i4,typeInt
<1> QED
  BY PTL, <1>2, <1>3


=========
