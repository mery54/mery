--------------------- MODULE TLAPROOFDOMAIN -----------------
EXTENDS Integers, Naturals,TLAPS
CONSTANT s,os,es
p | q == \E d \in 1..q : q = p * d
ASSUME s \in  [Nat -> Nat] /\ os \in  [Nat -> Nat] /\ es \in [Nat -> Nat]   
AXIOM  S0 ==  s[0]=0
AXIOM  Sn ==  \A p \in Nat : s[p+1]= s[p] + p+1
AXIOM  OS0 ==  os[0]=0
AXIOM  OSn ==  \A p \in Nat : IF ~((p+1) | 2)  THEN os[p+1]= os[p] + p+1 ELSE os[p]
AXIOM  ES0 ==  es[0]=0
AXIOM  ESn ==  \A p \in Nat : IF ((p+1) | 2 ) THEN es[p+1]= es[p] + p+1 ELSE es[p]
--------------------------------
(* LEMMAS for the three sequences  used s, es, os *)
LEMMA  SL1 == \A p \in Nat : 2*s[p+1]= (p*(p+1))
BY SMT
LEMMA  SL2 == \A p \in Nat : es[2*p]= 2*s[p]
BY SMT
LEMMA  SL3 == \A p \in Nat : es[2*p+1]= 2*s[p]
LEMMA  SL4 == \A p \in Nat : os[2*p]= p*p
LEMMA  SL5 == \A p \in Nat : os[2*p+1]= p*p
--------------------------------------
=============================== 