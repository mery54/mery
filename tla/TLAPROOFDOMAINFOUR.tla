--------------------- MODULE TLAPROOFDOMAINFOUR -----------------
EXTENDS Naturals, NaturalsInduction, TLAPS
-----------------------------------------------------------------
s[n \in Nat] == IF n=0 THEN 0 ELSE s[n-1]+n
-----------------------------------------------------------------
LEMMA sDefConclusion == NatInductiveDefConclusion(s, 0, LAMBDA v,n : v+n)
<1>1. NatInductiveDefHypothesis(s, 0, LAMBDA v,n : v+n)
  BY Zenon DEF NatInductiveDefHypothesis, s 
<1>. QED  BY <1>1, NatInductiveDef, Zenon

LEMMA  sType == s \in [Nat -> Nat]
<1>1. \A v \in Nat, n \in Nat \ {0} : v+n \in Nat
  OBVIOUS
<1>. QED
BY <1>1, NatInductiveDefType, sDefConclusion, Isa



LEMMA sDef == \A n \in Nat : s[n] = IF n=0 THEN 0 ELSE s[n-1] + n 
BY sDefConclusion DEF NatInductiveDefConclusion,s

THEOREM Mains == \A n \in Nat : 2 * s[n] = n * (n+1)
<1>. DEFINE P(n) == 2 * s[n] = n * (n+1)
<1>1. P(0)
  BY sDef
<1>2. ASSUME NEW n \in Nat, P(n) PROVE P(n+1)
  <2>1. 2 * s[n+1] = 2 * (s[(n+1)-1] + (n + 1))
    BY sDef
  <2>2. @ = 2 * s[n] + 2 * n + 2
    BY sType
  <2>3. @ = n * (n+1) + 2 * n + 2
    BY <1>2
  <2>. QED  BY <2>1, <2>2, <2>3
<1>. QED  BY <1>1, <1>2, NatInduction, Isa
-----------------------------------------------------------------

os[n \in Nat] == IF n=0 THEN 0 ELSE IF n % 2 = 0 THEN s[n-1] ELSE s[n-1]+n
es[n \in Nat] == IF n=0 THEN 0 ELSE IF n % 2 # 0 THEN s[n-1] ELSE s[n-1]+n
--------------------------------
(* LEMMAS for the three sequences  used s, es, os *)
LEMMA  SL1 == \A p \in Nat : 2*s[p+1]= (p*(p+1))
BY Mains, Isa

LEMMA  SL2 == \A p \in Nat : es[2*p]= 2*s[p]
BY SMT
LEMMA  SL3 == \A p \in Nat : es[2*p+1]= 2*s[p]
LEMMA  SL4 == \A p \in Nat : os[2*p]= p*p
LEMMA  SL5 == \A p \in Nat : os[2*p+1]= p*p
--------------------------------------

===========================================================================

