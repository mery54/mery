--------------------- MODULE TLAPROOFDOMAINbis -----------------
EXTENDS Integers, Naturals,TLAPS
CONSTANT s
ASSUME s \in  [Nat -> Nat]  
AXIOM  S0 ==  s[0]=0
AXIOM  Sn ==  \A p \in Nat : s[p+1]= s[p] + p+1
SUC(U) == {u \in Nat-{0}: u-1\in U}
----------------------------------------------------------------
(* Property to prove *)
P(u) == 2*s[u]= (u*(u+1))

LEMMA test == \A p \in Nat : 2*s[p+1]= (p*(p+1))

A == {n\in Nat: P(n)} 


LEMMA  RECP == P(0) /\ (\A n \in Nat : P(n) => P(n+1)) => (\A n \in Nat : P(n))
BY SMT

LEMMA REC == A \subseteq Nat /\ 0\in A /\ (SUC(A) \subseteq  A) =>  Nat \subseteq  A
BY RECP,SMT DEFS A


LEMMA une == \A n \in Nat :  (n*(n+1)) \div 2 + n + 1 = ((n+1)*(n+2)) \div 2
BY SMT

LEMMA deux == \A u,v,w \in Nat : u=v /\ v=w =>  u = w

      BY SMT


LEMMA help == \A n \in Nat :
          /\ s[n + 1] = s[n] + n + 1
          /\ 2 * s[n] = n * (n + 1)
          /\ 2 * s[n + 1] = (n + 1) * (n + 2)
          
          BY S0,Sn,SMT  

LEMMA trois == \A n \in Nat :  2*s[n]+ 2*(n + 1) = n*(n+1)+2*n+2

BY une,deux,SMT 


LEMMA un == \A n \in Nat : 
    /\ s[n+1]=  s[n] + n+1 
    /\ 2*s[n]= (n*(n+1))
    /\ 2*s[n+1]= ((n+1)*(n+2)) 

BY une,S0,Sn,Zenon,SMT,Isa

THEOREM NatInduction == 
  ASSUME P(0),
         \A n \in Nat : P(n) => P(n+1)
  PROVE  \A n \in Nat : P(n)


<1>1.  s[0]=0   BY S0,Sn, SMT  DEFS P
<1>2. P(0) BY <1>1,S0,Sn, SMT  DEFS P
<1>3. \A n \in Nat : P(n) => P(n+1) BY SMT DEFS P
<1>4. QED  BY <1>2,<1>3, S0,Sn,SMT  DEFS P

===============

