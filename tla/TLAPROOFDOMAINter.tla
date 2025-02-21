--------------------- MODULE TLAPROOFDOMAINter -----------------

EXTENDS Naturals, NaturalsInduction, TLAPS

s[n \in Nat] == IF n=0 THEN 0 ELSE s[n-1]+n




LEMMA sDefConclusion == NatInductiveDefConclusion(s, 0, LAMBDA v,n : v+n)
<1>1. NatInductiveDefHypothesis(s, 0, LAMBDA v,n : v+n)
  BY Zenon DEF NatInductiveDefHypothesis, s 
<1>. QED  BY <1>1, NatInductiveDef, Zenon


LEMMA sType == s \in [Nat -> Nat]
BY NatInductiveDefType, sDefConclusion, Isa  DEF s


LEMMA sDef == \A n \in Nat : s[n] = IF n=0 THEN 0 ELSE s[n-1] + n 
BY sDefConclusion DEF NatInductiveDefConclusion,s



THEOREM Main == \A n \in Nat : 2 * s[n] = n * (n+1)
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

===========================================================================

