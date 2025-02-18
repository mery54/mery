-------------------------------- MODULE TLAPROOFSUMVECTa-------------------
EXTENDS Naturals, Integers,TLC, TLAPS
---------------------------------------------------------------------
CONSTANTS n0
---------------------------------------------------------------------
typeInt(u) == u \in Int
pre(u) == u \in Nat /\  u # 0
v0 == [i \in 1..n0 |-> i] 
---------------------------------------------------
(* Computing the sum of elements in  vector v0 *)
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
CONSTANT defaultInitValue
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
---------------------    

i00 == (pc = "w2" => i <n /\  cu=u[i]) /\ (pc = "w1" => i <= n /\  cu=u[i])
i0 == typeInt(n) /\ typeInt(i) /\ typeInt(cu) /\ typeInt(r) /\ v=v0 /\ i \in 0..n0
i1 == pc = "w3" => cu=u[n] /\ i=n
InductiveInvariant == i1/\i0 /\ i00
------------------------------------------------------------------------
AXIOM U1 ==  u[0] = 0
AXIOM U2 ==   \A k \in 0..n0-1 : u[k+1] = u[k] + v0[k+1]

ASSUME Assumption == pre(n0) 

THEOREM InitProperty == Init => InductiveInvariant
<1> SUFFICES ASSUME Init
PROVE  InductiveInvariant
OBVIOUS
<1>1. n=n0 BY Assumption  DEF Init
<1>2.  pre(n0)  BY Assumption  DEF Init
<1>3. v=v0 BY  DEF Init
<1>4. i=0 BY  DEF Init
<1>5. cu  = 0 BY   DEF Init
<1>6. r \in Int  BY  DEF Init
<1>7. pc = "w1" BY DEF Init
<1>8. u[0] = 0 BY U1 DEF Init
<1>9. QED
BY  <1>1, <1>2,<1>3, <1>4,<1>5, <1>6,<1>7,<1>8   DEF InductiveInvariant, i1,i0,i00,w1, typeInt, pre, v0,U1,U2 

(* i1 *)

LEMMA  w1po1 ==
ASSUME  InductiveInvariant, w1
  PROVE  i1'

<1> USE DEF InductiveInvariant, i1,i0,i00,w1, typeInt, pre, v0,U1,U2 

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
     BY <1>b, U1,U2, SMT  DEFS InductiveInvariant, i1,i0,i00,w1, typeInt, pre, v0,U1,U2 
     <2>2 i1'
     BY <1>b,<2>1,U1, U2, SMT  DEFS InductiveInvariant, i1,i0,i00,w1, typeInt, pre, v0,U1,U2         
     <2> QED
     BY <1>b, <2>1,<2>2,SMT DEFS InductiveInvariant, i1,i0,i00,w1, typeInt, pre, v0,U1,U2 
<1>2 QED     
  BY <1>1, <1>a, <1>b,U1,U2 , SMT DEFS InductiveInvariant, i1,i0,i00,w1, typeInt, pre, v0,U1,U2 

LEMMA w2po1 ==
ASSUME  InductiveInvariant, w2
  PROVE  i1'
<1> USE DEF InductiveInvariant, i1,w2, typeInt, pre, v0  
<1>1 pc = "w2" /\ cu' = cu+v[i+1] /\ i' = i+1 /\ pc' = "w1" /\ UNCHANGED << n, v, r >>
     BY U2,SMT
<1>2 i1'
     BY <1>1, SMT
<1>3 QED
     BY <1>1, <1>2,SMT

LEMMA  w3po1 ==
ASSUME  InductiveInvariant,  w3
  PROVE  i1'
<1> USE DEF InductiveInvariant, i1,w3, typeInt, pre, v0, U1,U2  
<1>1  pc = "w3" /\ r' = cu /\ pc' = "Done" /\ UNCHANGED << n, v, i, cu >>
     BY U2,SMT
<1>2 i=n /\ cu=u[n]   BY U1,U2,SMT    
<1>3 i1'
     BY <1>1, <1>2, U2, SMT
<1>4 QED      BY <1>1, <1>2, <1>3, U2, SMT



LEMMA  Terminatingpo1 ==
ASSUME  InductiveInvariant, Terminating
  PROVE  i1'
<1> USE DEF InductiveInvariant, i1,w3, typeInt, pre, v0,vars  
<1>1  pc = "Done" /\ UNCHANGED vars 
     BY  SMT DEF Terminating
<1>2 i1'
     BY  SMT DEF Terminating
<1>3 QED
     BY <1>1, <1>2,SMT

stut == UNCHANGED vars

LEMMA  stutteringpo ==
ASSUME  InductiveInvariant,stut
  PROVE  i1'
<1> USE DEF InductiveInvariant, i1,  stut, typeInt, pre, v0,vars  
<1>1   i1'
     BY  SMT 
<1>2 QED
     BY <1>1,SMT

LEMMA NextP1 ==
ASSUME InductiveInvariant, Next
PROVE i1'

BY  w1po1,w2po1,w3po1, Terminatingpo1  DEFS Next,InductiveInvariant, i1,w1,w2,w3, Terminating,  typeInt, pre, v0,vars  




LEMMA  w1po0 ==
ASSUME  InductiveInvariant, w1
  PROVE  i0'

<1> USE DEF InductiveInvariant, i1,i0,i00,w1, typeInt, pre, v0,U1,U2 

<1>1 (i#n) \/ (i=n)
OBVIOUS

<1>a CASE i#n
     <2>1  pc' = "w2" /\ UNCHANGED << n, v, i, cu, r >>
     BY <1>a, SMT
     <2>2 i0'
     BY <1>a,<2>1, U1, U2, SMT     
     <2> QED
     BY <1>a, <2>1, <2>2, SMT
<1>b CASE i=n
     <2>1  pc="w1" /\ i= n /\ cu'=u[i'] /\ cu'=cu /\ i'=i /\ pc' = "w3" /\ UNCHANGED << n, v, i, cu, r >>
     BY <1>b, U1,U2, SMT  DEFS InductiveInvariant, i0,i0,i00,w1, typeInt, pre, v0,U1,U2 
     <2>2 i0'
     BY <1>b,<2>1,U1, U2, SMT  DEFS InductiveInvariant, i0,i0,i00,w1, typeInt, pre, v0,U1,U2         
     <2> QED
     BY <1>b, <2>1,<2>2,SMT DEFS InductiveInvariant, i0,i0,i00,w1, typeInt, pre, v0,U1,U2 
<1>2 QED     
  BY <1>1, <1>a, <1>b,U1,U2 , SMT DEFS InductiveInvariant, i0,i0,i00,w1, typeInt, pre, v0,U1,U2 

ggg
LEMMA w2po0 ==
ASSUME  InductiveInvariant, w2
  PROVE  i0'
<1> USE DEF InductiveInvariant, i0,w2, typeInt, pre, v0  
<1>1 i00/\ pc = "w2" /\ cu' = cu+v[i+1] /\ i' = i+1 /\ pc' = "w1" /\ UNCHANGED << n, v, r >>
     BY U2,SMT 
<1>2 i<n BY <1>1,SMT DEFS InductiveInvariant, i1,i0,i00,w2, typeInt, pre, v0,U1,U2   
<1>3 i<n0 BY <1>2,SMT DEFS InductiveInvariant, i1,i0,i00,w2, typeInt, pre, v0,U1,U2             
<1>4  i+1 <= n0 /\  i' \in 0..n0 BY <1>1, <1>3, SMT  DEFS InductiveInvariant, i1,i0,i00,w2, typeInt, pre, v0,U1,U2    
<1>5 i0'
     BY <1>1,<1>2,  SMT
<1>6 QED
     BY <1>1, <1>2,<1>3,Assumption,  SMT DEFS InductiveInvariant, i1,i0,i00,w2, typeInt, pre, v0,U1,U2   


LEMMA  w3po0 ==
ASSUME  InductiveInvariant,  w3
  PROVE  i0'
<1> USE DEF InductiveInvariant, i0,w3, typeInt, pre, v0, U1,U2  
<1>1  pc = "w3" /\ r' = cu /\ pc' = "Done" /\ UNCHANGED << n, v, i, cu >>  BY U2,SMT
<1>2  v'=v0    BY U1,U2,SMT DEFS  InductiveInvariant, i0,w3, typeInt, pre, v0, U1,U2   
<1>3  typeInt(n) /\ typeInt(i) /\ typeInt(cu) /\ typeInt(r)  BY U1,U2,SMT DEFS  InductiveInvariant, i0,w3, typeInt, pre, v0, U1,U2   
<1>4 i0' BY <1>1, <1>2, <1>3, U2, SMT DEFS  InductiveInvariant, i0,w3, typeInt, pre, v0, U1,U2   
<1>5 QED      BY <1>1, <1>2, <1>3, <1>4, U1, U2, SMT DEFS  InductiveInvariant, i0,w3, typeInt, pre, v0, U1,U2   



LEMMA  Terminatingpo0 ==
ASSUME  InductiveInvariant, Terminating
  PROVE  i0'
<1> USE DEF InductiveInvariant, i0,w3, typeInt, pre, v0,vars  
<1>1  pc = "Done" /\ UNCHANGED vars 
     BY  SMT DEF Terminating
<1>2 i0'
     BY  SMT DEF Terminating
<1>3 QED
     BY <1>1, <1>2,SMT

LEMMA  stutteringpo0 ==
ASSUME  InductiveInvariant,stut
  PROVE  i0'
<1> USE DEF InductiveInvariant, i0,  stut, typeInt, pre, v0,vars  
<1>1   i0'
     BY  SMT 
<1>2 QED
     BY <1>1,SMT


LEMMA NextP0 ==
ASSUME InductiveInvariant, Next
PROVE i0'

BY  w1po0,w2po0,w3po0, Terminatingpo0  DEFS Next,InductiveInvariant, i0,w1,w2,w3, Terminating,  typeInt, pre, v0,vars  


LEMMA  w1po00 ==
ASSUME  InductiveInvariant, w1
  PROVE  i00'
<1>. USE DEF InductiveInvariant, i1,i0,i00,w1, typeInt, pre, v0,U1,U2 
<1>1. (i#n) \/ (i=n)
OBVIOUS

<1>a. CASE i#n
     <2>1.  pc' = "w2" /\ i#n /\ UNCHANGED << n, v, i, cu, r >>
     BY <1>a, SMT  DEFS InductiveInvariant, i00,i00,i00,w1, typeInt, pre, v0,U1,U2 
     <2>2. (pc' = "w2" => i' <n' /\  cu'=u[i'])      BY <1>a,<2>1, U1,U2, SMT  DEFS InductiveInvariant, i1,i0,i00,w1, typeInt, pre, v0,U1,U2 
     <2>3.  (pc' = "w1" => i' <= n' /\  cu'=u[i']) BY <1>a,<2>1, U1,U2, SMT  DEFS InductiveInvariant, i1,i0,i00,w1, typeInt, pre, v0,U1,U2 
     <2>4.i00'
     BY <1>a,<2>1, <2>2, <2>3,U1, U2, SMT     
     <2> QED
     BY <1>a, <2>1, <2>2,<2>3,<2>4, SMT
<1>b CASE i=n
     <2>1  pc="w1" /\ i= n /\ cu'=u[i'] /\ cu'=cu /\ i'=i /\ pc' = "w3" /\ UNCHANGED << n, v, i, cu, r >>
     BY <1>b, U1,U2, SMT  DEFS InductiveInvariant, i00,i00,i00,w1, typeInt, pre, v0,U1,U2
     <2>2 pc' = "w3"
          BY <1>b, U1,U2, SMT  DEFS InductiveInvariant, i00,i00,i00,w1, typeInt, pre, v0,U1,U2
     <2>3. (pc' = "w2" => i' <n' /\  cu'=u[i'])      BY <1>b,<2>1, U1,U2, SMT  DEFS InductiveInvariant, i1,i0,i00,w1, typeInt, pre, v0,U1,U2 
     <2>4.  (pc' = "w1" => i' <= n' /\  cu'=u[i']) BY <1>b,<2>2, U1,U2, SMT  DEFS InductiveInvariant, i1,i0,i00,w1, typeInt, pre, v0,U1,U2 
     <2>5.i00'
     BY <1>b,<2>1, <2>2, <2>3,<2>4,U1, U2, SMT     
     <2> QED
     BY <1>b, <2>1, <2>2,<2>3,<2>4, <2>5,  SMT
<1>2 QED     
  BY <1>1, <1>a, <1>b,U1,U2 , SMT DEFS InductiveInvariant, i1,i0,i00,w1, typeInt, pre, v0,U1,U2 

========



LEMMA helpu == i \in 0..n0-1 =>   u[i+1]=u[i]+v0[i+1]
  BY U1,U2, SMT DEFS U1,U2,u,v0

LEMMA w2po00000 ==
ASSUME  InductiveInvariant, w2
  PROVE  i00'
<1>. USE DEF InductiveInvariant, i00,w2, typeInt, pre, v0  
<1>1. pc = "w2" /\ cu' = cu+v[i+1] /\ i' = i+1 /\ pc' = "w1" /\ UNCHANGED << n, v, r >>
     BY U2,SMT
<1>2. v=v0 /\  cu' = cu+v0[i+1]  
     BY <1>1,SMT DEFS InductiveInvariant, i1,i0,i00,w2, typeInt, pre,v0,U1,U2 
<1>3. i \in 0..n0-1 
     BY <1>1,SMT DEFS InductiveInvariant, i1,i0,i00,w2, typeInt, pre,v0,U1,U2 
<1>4. u[i+1]=u[i]+v0[i+1]
     BY <1>3,U1,U2,helpu,SMT DEFS InductiveInvariant, i1,i0,i00,w2,u, typeInt, pre,v0,U1,U2 
<1>5. i00'
     BY <1>1,<1>2,<1>3,<1>4, SMT
<1>6. QED
     BY <1>1, <1>2, <1>3, SMT


LEMMA w2po00 ==
ASSUME  InductiveInvariant, w2
  PROVE  i00'
<1> USE DEF InductiveInvariant, i00,w2, typeInt, pre, v0  
<1>1 pc = "w2" /\ cu' = cu+v[i+1] /\ i' = i+1 /\ pc' = "w1" /\ UNCHANGED << n, v, r >>
       BY U1,U2,SMT DEFS  InductiveInvariant, i00,w3, typeInt, pre, v0, U1,U2   
<1>2 cu = u[i] /\ v = v0
     BY U1,U2,SMT DEFS  InductiveInvariant, i00,w3, typeInt, pre, v0, U1,U2   
<1>3 cu +v[i+1] = u[i+1]
     BY U1,U2,SMT DEFS  InductiveInvariant, i00,w3, typeInt, pre, v0, U1,U2   
<1>4 i00'
     BY <1>1, SMT
<1>6 QED
     BY <1>1, <1>2,<1>3, SMT

LEMMA  w3po00 ==
ASSUME  InductiveInvariant,  w3
  PROVE  i00'
<1> USE DEF InductiveInvariant, i00,w3, typeInt, pre, v0, U1,U2  
<1>1  pc = "w3" /\ r' = cu /\ pc' = "Done" /\ UNCHANGED << n, v, i, cu >>
     BY U2,SMT
<1>2 (pc' = "w2" => i' <n' /\  cu'=u[i'])      BY U2,SMT
<1>3  (pc' = "w1" => i' <= n' /\  cu'=u[i'])      BY U2,SMT
<1>4 i=n /\ cu=u[n]   BY U1,U2,SMT    
<1>5 i00'
     BY <1>1, <1>2, U2, SMT
<1>6 QED      BY <1>1, <1>2, <1>3, U2, SMT

LEMMA  Terminatingpo00 ==
ASSUME  InductiveInvariant, Terminating
  PROVE  i00'
<1> USE DEF InductiveInvariant, i00,w3, typeInt, pre, v0,vars  
<1>1  pc = "Done" /\ UNCHANGED vars 
     BY  SMT DEF Terminating
<1>2 i00'
     BY  SMT DEF Terminating
<1>3 QED
     BY <1>1, <1>2,SMT

LEMMA  stutteringpo00 ==
ASSUME  InductiveInvariant,stut
  PROVE  i00'
<1> USE DEF InductiveInvariant, i00,  stut, typeInt, pre, v0,vars  
<1>1   i00'
     BY  SMT 
<1>2 QED
     BY <1>1,SMT

LEMMA NextP00 ==
ASSUME InductiveInvariant, Next
PROVE i00'

BY  w1po00,w2po00,w3po00, Terminatingpo00  DEFS Next,InductiveInvariant, i00,w1,w2,w3, Terminating,  typeInt, pre, v0,vars  

====================

LEMMA NextP ==
ASSUME InductiveInvariant, Next
PROVE InductiveInvariant'

BY   NextP1,NextP0, NextP00, DEFS InductiveInvariant, Next, i0,i00,  i1,w1,w2,w3, Terminating,  typeInt, pre, v0,vars  



LEMMA NNextInvariant ==
ASSUME InductiveInvariant,  [Next]_vars
PROVE InductiveInvariant'

BY NextP,stutteringpo, PTL DEF Next, stut, InductiveInvariant,vars       


THEOREM INV ==  InductiveInvariant /\   [Next]_vars => InductiveInvariant'
BY NNextInvariant DEFS InductiveInvariant, i1,w1,w2,w3, Terminating,  typeInt, pre, v0,vars  


THEOREM Invariance == Spec => [] InductiveInvariant
<1>1 InductiveInvariant /\   [Next]_vars => InductiveInvariant'
  BY INV  DEF InductiveInvariant, i1,w1,w2,w3, Terminating,  typeInt, pre, v0,vars  
<1>2 Init => InductiveInvariant
BY InitProperty   DEF InductiveInvariant, i1,w1,w2,w3, Terminating,  typeInt, pre, v0,vars  
<1>3 Spec => []InductiveInvariant
  BY PTL, InitProperty, NextP, <1>1 DEF Spec,InductiveInvariant, i1,w1,w2,w3, Terminating,  typeInt, pre, v0,vars  
<1> QED
  BY PTL, <1>2, <1>3

=========
