
LEMMA  w1po0 ==
ASSUME  InductiveInvariant, w1
  PROVE  i1'

<1> USE DEF InductiveInvariant, i1,w1, typeInt, pre, v0

<1>1 (i#n) \/ (i=n)
OBVIOUS

<1>a CASE i#n
     <2>1  pc' = "w2" /\ UNCHANGED << n, v, i, cu, r >>
     BY <1>a, SMT
     <2>2 i1'
     BY <1>a,<2>1, SMT     
     <2> QED
     BY <1>a, <2>1, <2>2, SMT
<1>b CASE i=n
     <2>1  pc' = "w3" /\ UNCHANGED << n, v, i, cu, r >>
     BY <1>b, SMT
     <2>2 i1'
     BY <1>b,<2>1,SMT          
     <2> QED
     BY <1>b, <2>1,<2>2,SMT
<1>2 QED     
  BY <1>1, <1>a, <1>b, SMT

LEMMA w2po0 ==
ASSUME  InductiveInvariant, w2
  PROVE  i1'
<1> USE DEF InductiveInvariant, i1,w2, typeInt, pre, v0  
<1>1 pc = "w2" /\ cu' = cu+v[i+1] /\ i' = i+1 /\ pc' = "w1" /\ UNCHANGED << n, v, r >>
     BY SMT
<1>2 i0'
     BY <1>1, SMT
<1>3 QED
     BY <1>1, <1>2,SMT

LEMMA  w3po0 ==
ASSUME  InductiveInvariant,  w3
  PROVE  i0'
<1> USE DEF InductiveInvariant, i0,w3, typeInt, pre, v0  
<1>1  pc = "w3" /\ r' = cu /\ pc' = "Done" /\ UNCHANGED << n, v, i, cu >>
     BY SMT
<1>2 i0'
     BY <1>1, SMT
<1>3 QED
     BY <1>1, <1>2,SMT



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

stut == UNCHANGED vars

LEMMA  stutteringpo ==
ASSUME  InductiveInvariant,stut
  PROVE  i0'
<1> USE DEF InductiveInvariant, i0,  stut, typeInt, pre, v0,vars  
<1>1   i0'
     BY  SMT 
<1>2 QED
     BY <1>1,SMT

LEMMA NextP1 ==
ASSUME InductiveInvariant, Next
PROVE i0'

BY  w1po0,w2po0,w3po0, Terminatingpo0  DEFS Next,InductiveInvariant, i0,w1,w2,w3, Terminating,  typeInt, pre, v0,vars  



