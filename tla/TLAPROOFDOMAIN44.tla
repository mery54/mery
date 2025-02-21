




LEMMA une == \A n \in Nat :  (n*(n+1)) \div 2 + n + 1 = ((n+1)*(n+2)) \div 2
      BY SMT

LEMMA un == \A n \in Nat :  2*(n*(n+1))  + 2*n + 2 = (n+1)*(n+2)
      BY SMT

LEMMA deux == \A u,v,w \in Nat : u=v /\ v=w =>  u = w
      BY SMT

LEMMA help == \A n \in Nat :
          /\ s[n + 1] = s[n] + n + 1
          /\ 2 * s[n] = n * (n + 1)
          /\ 2 * s[n + 1] = (n + 1) * (n + 2)

BY S0,Sn, SMT 

LEMMA trois == \A n \in Nat :  2*s[n]+ 2*(n + 1) = n*(n+1)+2*n+2
      BY une,deux,SMT 


LEMMA quatre == \A n \in Nat : 
    /\ s[n+1]=  s[n] + n+1 
    /\ 2*s[n]= (n*(n+1))
    /\ 2*s[n+1]= ((n+1)*(n+2)) 

BY S0,Sn 

THEOREM NatInduction == 
  ASSUME P(0),
         \A n \in Nat : P(n) => P(n+1)
  PROVE  \A n \in Nat : P(n)


<1>1.  s[0]=0   BY S0,Sn, SMT  DEFS P
<1>2. P(0) BY <1>1,S0,Sn, SMT  DEFS P
<1>3. \A n \in Nat : P(n) => P(n+1) BY  help, quatre, SMT DEFS P
<1>4. QED  BY <1>2,<1>3, S0,Sn,SMT  DEFS P

===============

