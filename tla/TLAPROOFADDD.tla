---------------------------- MODULE TLAPROOFADDD ----------------------------
EXTENDS Integers, TLANaturalsInduction, TLAPS

VARIABLE x 

Init == x = 0 
Next == x' = x + 1

Spec == Init /\ [][Next]_x /\ WF_x(Next)

THEOREM
    \A n \in Nat:  Spec => <>(x = n)
PROOF

<1> DEFINE Inv == x \in Nat 

<1>1. Spec => []Inv 
    <2>1. Init => Inv 
           BY DEF Init, Inv
    <2>2. Inv /\ [Next]_x => Inv'
    
        BY DEF Inv, Next
    <2> QED
        BY <2>1, <2>2, PTL DEF Spec

<1> DEFINE P(m) == Spec => <>(x = m)
<1> HIDE DEF P  
<1>2. \A n \in Nat:  P(n)

    <2>1. P(0)
        BY PTL DEF P, Spec, Init

<2>2. \A n \in Nat:  P(n) => P(n + 1)
        <3>1. SUFFICES
                ASSUME NEW n \in Nat
                PROVE (Spec /\ <>(x = n)) => <>(x = n + 1)
             BY <3>1 DEF P
        <3>2. Spec => [] \/ ~ (x = n)
                         \/ [] (x = n)
                         \/ <> (x = n + 1)
            <4>1. ASSUME Inv /\ [Next]_x
                  PROVE  \/ ~ (x = n)
                         \/ (x = n)'
                         \/ (x = n + 1)'
                BY <4>1 DEF Inv, Next
		<4> QED
                BY <1>1, <4>1, PTL DEF Spec
		<4>1. ASSUME Inv
                  PROVE ENABLED <<Next>>_x
                BY <4>1, ExpandENABLED DEF Next, Inv
            <4>2. ASSUME []Inv
                  PROVE WF_x(Next) => []<><<Next>>_x
                BY <4>1, <4>2, PTL
             <4> QED
                BY <1>1, <4>2 DEF Spec
          <3>4. ASSUME Inv /\ (x = n) /\ <<Next>>_x
              PROVE ~(x = n)'
            BY <3>4 DEF Inv, Next
        <3> QED
            BY <1>1, <3>2, <3>3, <3>4, PTL
    <2> QED
        BY <2>1, <2>2, NatInduction
<1> QED
    BY <1>2 DEF P


================================================================================