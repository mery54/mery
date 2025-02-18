
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
<1> USE DEF InductiveInvariant, i1,w3, typeInt, pre, v0  
<1>1  pc = "w3" /\ r' = cu /\ pc' = "Done" /\ UNCHANGED << n, v, i, cu >>
     BY SMT
<1>2 i1'
     BY <1>1, SMT
<1>3 QED
     BY <1>1, <1>2,SMT



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
