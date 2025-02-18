-------------------------------- MODULE TLAPROOFVECTSUM -------------------
EXTENDS Naturals, Integers, TLAPS
---------------------------------------------------------------------
CONSTANTS n0,v0
---------------------------------------------------------------------
typeInt(u) == u \in Int
pre(u,v) == u \in Nat /\  u # 0 /\ v \in [1..n0 -> Int]
\* v0 == [i \in 1..n0 |-> i]
---------------------------------------------------------------------
(*
--algorithm sumvect  {
variables  n=n0,v=v0,i=0,cu=0,r;
{
w1:while (i # n) {
  w2:cu:=cu+v[i+1];
  i:=i+1;
};
w3:r:=cu;
}
}
*)


\* BEGIN TRANSLATION (chksum(pcal) = "42832d85" /\ chksum(tla) = "19fa4b63")
\* CONSTANT defaultInitValue
VARIABLES n, v, i, cu, r, pc

vars == << n, v, i, cu, r, pc >>

Init == (* Global variables *)
        /\ n = n0
        /\ v = v0
        /\ i = 0
        /\ cu = 0
        /\ r \in Int 
        /\ pc = "w1"

w1 == /\ pc = "w1"
      /\ IF i # n
            THEN /\ pc' = "w2"
            ELSE /\ pc' = "w3"
      /\ UNCHANGED << n, v, i, cu, r >>

w2 == /\ pc = "w2"
      /\ cu' = cu+v[i+1]
      /\ i' = i+1
      /\ pc' = "w1"
      /\ UNCHANGED << n, v, r >>

w3 == /\ pc = "w3"
      /\ r' = cu
      /\ pc' = "Done"
      /\ UNCHANGED << n, v, i, cu >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == w1 \/ w2 \/ w3
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 


---------------------    
u[k \in 0..n0] == IF k=0 THEN  0  ELSE  u[k-1]+v0[k]
i00 ==   cu=u[i] /\ (pc="w1" => i \leq n) /\ (pc="w2" => i < n) /\ (pc="w3" => i =  n) 
i0 == typeInt(n) /\ typeInt(i) /\ typeInt(cu) /\ typeInt(r) /\ v=v0 /\ n=n0 /\ i \in 0..n0
\* i2 == cu=u[i]
i1 == pc = "w3" => cu=u[n] /\ i=n

InductiveInvariant == i1/\i0/\i00 
------------------------------------------------------------------------


AXIOM U1 ==  u[0] = 0
AXIOM U2 ==   \A k \in 0..n0-1 : u[k+1] = u[k] + v0[k+1]

ASSUME Assumption == pre(n0,v0) 

THEOREM InitProperty == Init => InductiveInvariant
<1> SUFFICES ASSUME Init
PROVE  InductiveInvariant
OBVIOUS
<1>1. n=n0 BY Assumption  DEF Init
<1>2.  pre(n0,v0)  BY Assumption  DEF Init
<1>3. v=v0 BY  DEF Init
<1>4. i=0 BY  DEF Init
<1>5. cu  = 0 BY   DEF Init
<1>6. r \in Int  BY  DEF Init
<1>7. pc = "w1" BY DEF Init
<1>8. cu=u[0] BY U1 DEF Init
<1>9. (pc="w1" => i \leq n) BY <1>1, <1>2, <1>4, <1>7,SMT  DEF Init,pre,i00,i0,i1
<1>10. (pc="w2" => i < n) BY DEF Init
<1>11. (pc="w3" => i =  n)  BY DEF Init
<1>12. QED BY  <1>1, <1>2,<1>3, <1>4,<1>5, <1>6,<1>7,<1>8, <1>9, <1>10, <1>11 DEF InductiveInvariant, i1,i0,i00,w1, typeInt, pre 


(*
THEOREM Init => InductiveInvariant
BY Assumption DEF Init, InductiveInvariant, i1, typeInt, pre

*)

\* start 

LEMMA  w1po1 ==
ASSUME  InductiveInvariant, w1
  PROVE  i1'

<1> USE DEF InductiveInvariant, i1,i0,i00,w1, typeInt, pre 

<1>1 (i#n) \/ (i=n)
OBVIOUS

<1>a CASE i#n
     <2>1  pc' = "w2" /\ UNCHANGED << n, v, i, cu, r >>
     BY <1>a, SMT
     <2>2 i1'
     BY <1>a,<2>1, U1, U2, SMT     
     <2> QED
     BY <1>a, <2>1, <2>2, SMT
<1>b CASE i=n
     <2>1  pc="w1" /\ i= n /\ cu'=u[i'] /\ cu'=cu /\ i'=i /\ pc' = "w3" /\ UNCHANGED << n, v, i, cu, r >>
     BY <1>b, U1,U2, SMT  DEFS InductiveInvariant, i1,i0,i00,w1, typeInt, pre 
     <2>2 i1'
     BY <1>b,<2>1,U1, U2, SMT  DEFS InductiveInvariant, i1,i0,i00,w1, typeInt, pre        
     <2> QED
     BY <1>b, <2>1,<2>2,SMT DEFS InductiveInvariant, i1,i0,i00,w1, typeInt, pre
<1>2 QED     
  BY <1>1, <1>a, <1>b,U1,U2 , SMT DEFS InductiveInvariant, i1,i0,i00,w1, typeInt, pre

LEMMA w2po1 ==
ASSUME  InductiveInvariant, w2
  PROVE  i1'
<1> USE DEF InductiveInvariant, i1,w2, typeInt, pre  
<1>1 pc = "w2" /\ cu' = cu+v[i+1] /\ i' = i+1 /\ pc' = "w1" /\ UNCHANGED << n, v, r >>
     BY U2,SMT
<1>2 i1'
     BY <1>1, SMT
<1>3 QED
     BY <1>1, <1>2,SMT

LEMMA  w3po1 ==
ASSUME  InductiveInvariant,  w3
  PROVE  i1'
<1> USE DEF InductiveInvariant, i1,w3, typeInt, pre 
<1>1  pc = "w3" /\ r' = cu /\ pc' = "Done" /\ UNCHANGED << n, v, i, cu >>
     BY U2,SMT
<1>2 i=n /\ cu=u[n]   BY U1,U2,SMT    
<1>3 i1'
     BY <1>1, <1>2, U2, SMT
<1>4 QED      BY <1>1, <1>2, <1>3, U2, SMT



LEMMA  Terminatingpo1 ==
ASSUME  InductiveInvariant, Terminating
  PROVE  i1'
<1> USE DEF InductiveInvariant, i1,w3, typeInt, pre,vars  
<1>1  pc = "Done" /\ UNCHANGED vars 
     BY  SMT DEF Terminating
<1>2 i1'
     BY  SMT DEF Terminating
<1>3 QED
     BY <1>1, <1>2,SMT

stut == UNCHANGED vars

LEMMA  stutteringpo1 ==
ASSUME  InductiveInvariant,stut
  PROVE  i1'
<1> USE DEF InductiveInvariant, i1,  stut, typeInt, pre,vars  
<1>1   i1'
     BY  SMT 
<1>2 QED
     BY <1>1,SMT

LEMMA NextP1 ==
ASSUME InductiveInvariant, Next
PROVE i1'

BY  w1po1,w2po1,w3po1, Terminatingpo1  DEFS Next,InductiveInvariant, i1,w1,w2,w3, Terminating,  typeInt, pre,vars  


\* end

-------------------------------

\* i0



LEMMA  w1po0 ==
ASSUME  InductiveInvariant, w1
  PROVE  i0'

<1> USE DEF InductiveInvariant, i0,w1, typeInt, pre

<1>1 (i#n) \/ (i=n)
OBVIOUS

<1>a CASE i#n
     <2>1  pc' = "w2" /\ UNCHANGED << n, v, i, cu, r >>
     BY <1>a, SMT
     <2>2 i0'
     BY <1>a,<2>1, SMT     
     <2> QED
     BY <1>a, <2>1, <2>2, SMT
<1>b CASE i=n
     <2>1  pc' = "w3" /\ UNCHANGED << n, v, i, cu, r >>
     BY <1>b, SMT
     <2>2 i0'
     BY <1>b,<2>1,SMT          
     <2> QED
     BY <1>b, <2>1,<2>2,SMT
<1>2 QED     
  BY <1>1, <1>a, <1>b, SMT


LEMMA w2po0 ==
ASSUME  InductiveInvariant, w2
  PROVE  i0'
<1> USE DEF InductiveInvariant, i0,w2, typeInt, pre,u  
<1>1 pc = "w2"  /\ UNCHANGED << n, v, r >>
     BY SMT
<1>2 typeInt(n) /\ typeInt(i) /\ typeInt(cu) /\ typeInt(r) /\ v=v0   /\  i \in 0..n0 /\  UNCHANGED << n, v, r >>
     BY U1,SMT  DEFS  InductiveInvariant, i0,i1,i00,w2, typeInt, pre,u
<1>3 typeInt(n') /\ typeInt(i') /\ typeInt(cu') /\ typeInt(r') /\ v'=v0  /\  UNCHANGED << n, v, r >>
     BY SMT  DEFS InductiveInvariant, i0,w2, typeInt, pre,u
<1>4  i<n /\ i'=i+1
     BY SMT  DEFS InductiveInvariant, i0,i1,i00,w2, typeInt, pre,u
<1>5  i \in 0..n0  /\ i < n
     BY  <1>1,<1>2, SMT DEFS  InductiveInvariant, i0,i1,i00,w2, typeInt, pre,u
<1>6  n=n0 /\  i < n0
     BY  <1>1,<1>5,<1>3, SMT DEFS  InductiveInvariant, i0,i1,i00,w2, typeInt, pre,u
<1>7  i \in 0.. n0-1
     BY  <1>1,<1>5,<1>6, SMT DEFS  InductiveInvariant, i0,i1,i00,w2, typeInt, pre,u
<1>8  i' \in 0.. n0
     BY  <1>1,<1>5,<1>6,<1>7, SMT DEFS  InductiveInvariant, i0,i1,i00,w2, typeInt, pre,u
<1>9  n'=n0 /\ v'=v0
     BY  <1>1,<1>2,SMT DEFS  InductiveInvariant, i0,i1,i00,w2, typeInt, pre,u                         
<1>20 i0'
     BY <1>1,<1>2, <1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9, SMT DEFS InductiveInvariant, i0,i1,i00,w2, typeInt, pre,u
<1>21 QED
     BY <1>1,<1>2, <1>3,<1>4,<1>5,<1>6,<1>7,<1>8,<1>9,  <1>20,SMT DEFS InductiveInvariant, i0,i1,i00,w2, typeInt, pre,u
     




LEMMA  w3po0 ==
ASSUME  InductiveInvariant,  w3
  PROVE  i0'
<1> USE DEF InductiveInvariant, i0,i1,i00, w3, typeInt, pre
<1>1  pc = "w3" /\ r' = cu /\ pc' = "Done" /\ UNCHANGED << n, v, i, cu >>
     BY U1, U2,SMT DEFS InductiveInvariant, i0,i1,i00, w3, typeInt, pre 
<1>2 i=n /\ cu=u[n]   BY U1,U2,SMT  DEFS InductiveInvariant, i0,i1, i00, w3, typeInt, pre   
<1>3 i0'
     BY <1>1, <1>2, U1, U2, SMT DEFS InductiveInvariant, i0,i1,i00,w3, typeInt, pre 
<1>4 QED      BY <1>1, <1>2, <1>3, U1, U2, SMT DEFS InductiveInvariant, i0,i1,i00, w3, typeInt, pre 




LEMMA  Terminatingpo0 ==
ASSUME  InductiveInvariant, Terminating
  PROVE  i0'
<1> USE DEF InductiveInvariant, i0,w3, typeInt, pre,vars  
<1>1  pc = "Done" /\ UNCHANGED vars 
     BY  SMT DEF Terminating
<1>2 i0'
     BY  SMT DEF Terminating
<1>3 QED
     BY <1>1, <1>2,SMT



LEMMA  stutteringpo0 ==
ASSUME  InductiveInvariant,stut
  PROVE  i0'
<1> USE DEF InductiveInvariant, i0,  stut, typeInt, pre,vars  
<1>1   i0'
     BY  SMT 
<1>2 QED
     BY <1>1,SMT

LEMMA NextP0 ==
ASSUME InductiveInvariant, Next
PROVE i0'

BY  w1po0,w2po0,w3po0, Terminatingpo0  DEFS Next,InductiveInvariant, i0,w1,w2,w3, Terminating,  typeInt, pre,vars  


\* i0

--------------------------
\* i00



LEMMA  w1po00 ==
ASSUME  InductiveInvariant, w1
  PROVE  i00'

<1> USE DEF InductiveInvariant, i00,i1,i0,w1, typeInt, pre 

<1>1 (i#n) \/ (i=n)
OBVIOUS

<1>a CASE i#n
     <2>1  pc' = "w2" /\ UNCHANGED << n, v, i, cu, r >>
     BY <1>a, SMT
     <2>2 i1'
     BY <1>a,<2>1, U1, U2, SMT     
     <2> QED
     BY <1>a, <2>1, <2>2, SMT
<1>b CASE i=n
     <2>1  pc="w1" /\ i= n /\ cu'=u[i'] /\ cu'=cu /\ i'=i /\ pc' = "w3" /\ UNCHANGED << n, v, i, cu, r >>
     BY <1>b, U1,U2, SMT  DEFS InductiveInvariant, i1,i0,i00,w1, typeInt, pre 
     <2>2 i00'
     BY <1>b,<2>1,U1, U2, SMT  DEFS InductiveInvariant, i1,i0,i00,w1, typeInt, pre        
     <2> QED
     BY <1>b, <2>1,<2>2,SMT DEFS InductiveInvariant, i1,i0,i00,w1, typeInt, pre 
<1>2 QED     
  BY <1>1, <1>a, <1>b,U1,U2 , SMT DEFS InductiveInvariant, i1,i0,i00,w1, typeInt, pre 



LEMMA  w3po00 ==
ASSUME  InductiveInvariant,  w3
  PROVE  i00'
<1> USE DEF InductiveInvariant, i0,i1,i00, w3, typeInt, pre
<1>1  pc = "w3" /\ r' = cu /\ pc' = "Done" /\ UNCHANGED << n, v, i, cu >>
     BY U1, U2,SMT DEFS InductiveInvariant, i0,i1,i00, w3, typeInt, pre 
<1>2 i=n /\ cu=u[n]   BY U1,U2,SMT  DEFS InductiveInvariant, i0,i1, i00, w3, typeInt, pre   
<1>3 i00'
     BY <1>1, <1>2, U1, U2, SMT DEFS InductiveInvariant, i0,i1,i00,w3, typeInt, pre 
<1>4 QED      BY <1>1, <1>2, <1>3, U1, U2, SMT DEFS InductiveInvariant, i0,i1,i00, w3, typeInt, pre 





LEMMA w2po00 ==
ASSUME  InductiveInvariant, w2
  PROVE  i00'
<1> USE DEF InductiveInvariant, i00,i0,i1,w2, typeInt, pre 
<1>1 pc = "w2" /\ UNCHANGED << n, v, r >> 
     BY SMT DEFS InductiveInvariant, i00,i0,i1,w2, typeInt, pre
<1>2  v=v0 /\ n=n0 
     BY SMT DEFS InductiveInvariant, i00,i0,i1,w2, typeInt, pre
<1>3  v'=v0  BY <1>1, <1>2, SMT DEFS InductiveInvariant, i00,i0,i1,w2, typeInt, pre
<1>4   n'=n0  BY <1>1, <1>2, SMT DEFS InductiveInvariant, i00,i0,i1,w2, typeInt, pre
<1>5  cu = u[i] BY <1>1, <1>2, U1,U2, SMT DEFS InductiveInvariant, i00,i0,i1,w2, typeInt, pre,u
<1>6  cu' = cu + v0[i+1] BY <1>1,<1>2, U1,U2,  SMT DEFS InductiveInvariant, i00,i0,i1,w2, typeInt, pre,u
<1>7   i'=i+1
      BY <1>1, <1>2, U1,U2, Isa, SMT DEFS InductiveInvariant, i00,i0,i1,w2, typeInt, pre,u
<1>8   u[i'] = u[i+1] /\ i \in 0..n0-1
      BY <1>1, <1>2,<1>4, <1>5, U1,U2, Isa, SMT DEFS InductiveInvariant, i00,i0,i1,w2, typeInt, pre,u
<1>9     u[i+1] = u[i] + v0[i+1] 
      BY  U1,U2,  SMT DEFS InductiveInvariant, i00,i0,i1,w2, typeInt, pre,u
<1>10  cu' = u[i'] /\ u[i'] = u[i+1] /\ u[i+1] = u[i] + v0[i+1]
      BY <1>1, <1>2,  U1,U2, Isa, SMT DEFS InductiveInvariant, i00,i0,i1,w2, typeInt, pre                        
<1>11   (pc="w1" => i \leq n)  /\ i \leq n /\  (pc'="w1" => i' \leq n')  /\ i' \leq n' 
       BY <1>1,<1>2, SMT DEFS InductiveInvariant, i00,i0,i1,w2, typeInt, pre,U1,U2      
<1>12  (pc="w2" => i < n) /\ (pc'="w2" => i' < n')
      BY <1>1, <1>2, U1,U2, SMT DEFS InductiveInvariant, i00,i0,i1,w2, typeInt, pre

<1>13   (pc="w3" => i =  n) /\  (pc'="w3" => i' =  n')
      BY <1>1, <1>2, U1,U2, SMT DEFS InductiveInvariant, i00,i0,i1,w2, typeInt, pre

<1>14 i00'
     BY <1>1, <1>2, <1>3,<1>4,<1>5,<1>6, <1>7,<1>8,<1>9,<1>10, <1>11 ,  U1, U2, SMT DEFS InductiveInvariant, i00,i0,i1,w2, typeInt, pre
<1>15 QED
     BY  <1>1, <1>2, <1>3,<1>4, <1>5,<1>6, <1>7,  <1>8,<1>9, <1>10,<1>11,<1>12 , SMT DEFS InductiveInvariant, i00,i0,i1,w2, typeInt, pre




LEMMA  Terminatingpo00 ==
ASSUME  InductiveInvariant, Terminating
  PROVE  i00'
<1> USE DEF InductiveInvariant, i00,w3, typeInt, pre,vars  
<1>1  pc = "Done" /\ UNCHANGED vars 
     BY  SMT DEF Terminating
<1>2 i00'
     BY  SMT DEF Terminating
<1>3 QED
     BY <1>1, <1>2,SMT



LEMMA  stutteringpo00 ==
ASSUME  InductiveInvariant,stut
  PROVE  i00'
<1>1   i00'
     BY  SMT DEFS InductiveInvariant, i1,i0,i00,  stut, typeInt, pre,vars 
<1>2 QED
     BY <1>1,SMT DEFS InductiveInvariant, i1,i0,i00,  stut, typeInt, pre,vars 


LEMMA NextP00 ==
ASSUME InductiveInvariant, Next
PROVE i00'

BY  w1po00,w2po00,w3po00, Terminatingpo00  DEFS Next,InductiveInvariant, i0,w1,w2,w3, Terminating,  typeInt, pre,vars  




LEMMA NextP ==
ASSUME InductiveInvariant, Next
PROVE InductiveInvariant'

BY  U1,U2, NextP1, NextP0, NextP00, SMT DEFS Next, InductiveInvariant, i1,i0,i00,w1,w2,w3, Terminating,  typeInt, pre,u  


LEMMA NNextInvariant ==
ASSUME InductiveInvariant,  [Next]_vars
PROVE InductiveInvariant'

BY  NextP,stutteringpo1,stutteringpo0,stutteringpo00, PTL, SMT DEFS Next, InductiveInvariant, i1,i0,i00, Terminating,  typeInt, pre,u,vars  


THEOREM INV ==  InductiveInvariant /\   [Next]_vars => InductiveInvariant'
BY NNextInvariant DEFS InductiveInvariant, i1,w1,w2,w3, Terminating,  typeInt, pre,vars  


THEOREM Invariance == Spec => [] InductiveInvariant
<1>1 InductiveInvariant /\   [Next]_vars => InductiveInvariant'
  BY INV  DEF InductiveInvariant, i1,w1,w2,w3, Terminating,  typeInt, pre,vars  
<1>2 Init => InductiveInvariant
BY InitProperty   DEF InductiveInvariant, i1,w1,w2,w3, Terminating,  typeInt, pre,vars  
<1>3 Spec => []InductiveInvariant
  BY PTL, InitProperty, NextP, <1>1 DEF Spec,InductiveInvariant, i1,w1,w2,w3, Terminating,  typeInt, pre,vars  
<1> QED
  BY PTL, <1>2, <1>3

=========
