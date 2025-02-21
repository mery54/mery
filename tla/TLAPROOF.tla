---------------MODULE TLAPROOF----------------

EXTENDS TLAPROOFDOMAIN

CONSTANTS n
pre(u) == u >= 0


\* BEGIN TRANSLATION (chksum(pcal) = "a9fed7e7" /\ chksum(tla) = "f1896d17")
VARIABLES rs, re, input, cur, ce, cs, pc

vars == << rs, re, input, cur, ce, cs, pc >>

Init == (* Global variables *)
        /\ rs = 0
        /\ re = 0
        /\ input = n
        /\ cur = 0
        /\ ce = 0
        /\ cs = 0
        /\ pc = "w"

w == /\ pc = "w"
     /\ IF cur # n
           THEN /\ IF cur % 2 # 0
                      THEN /\ cs' = cs+cur+1
                           /\ ce' = ce+cur+1
                           /\ cur' = cur+1
                      ELSE /\ cs' = cs+cur+1
                           /\ ce' = ce
                           /\ cur' = cur+1
                /\ pc' = "w"
           ELSE /\ pc' = "Done"
                /\ UNCHANGED << cur, ce, cs >>
     /\ UNCHANGED << rs, re, input >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == w
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 


i1 == 
    /\ ( (pc = "w") => (cs = (cur*(cur+1)) \div 2))   
    /\   ((pc = "Done") => (cs = (n*(n+1)) \div 2))


InductiveInvariant == i1
ASSUME Assumption == pre(n)

THEOREM InitProperty == Init => InductiveInvariant
<1> SUFFICES ASSUME Init
PROVE  InductiveInvariant
OBVIOUS
<1>1. ce=0 BY Assumption  DEF Init
<1>2. cs=0  BY Assumption  DEF Init
<1>3. re = 0 BY Assumption  DEF Init
<1>4. pc="w"  BY Assumption  DEF Init
<1>5. rs= 0  BY Assumption  DEF Init
<1>6. cur= 0  BY Assumption  DEF Init
<1>. QED
BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6   DEF InductiveInvariant,pre

THEOREM Init => InductiveInvariant
BY Assumption DEF Init, InductiveInvariant, pre

LEMMA truc ==
ASSUME  InductiveInvariant, w
  PROVE  InductiveInvariant'
BY DEFS InductiveInvariant,w

LEMMA  wpo1 ==
ASSUME  InductiveInvariant, w1
  PROVE  i1'
<1>. USE DEF InductiveInvariant, i1,i0,w1, typeInt, pre
<1>1.  a = a0 /\  b = b0 /\ ((a<b) \/ (a >=b))  BY  SMT  DEFS InductiveInvariant, i1,i0,w1, typeInt, pre,maximum
<1>a. CASE a <  b
     <2>1.  pc="w1" /\ a<b /\ r'=b /\ pc' = "Done" /\ UNCHANGED << a, b>>
     BY <1>a,  SMT  DEFS InductiveInvariant, i1,i0,w1, typeInt, pre,maximum
     <2>2.  pc' = "Done" => r' =maximum(a0,b0)
     BY <1>a, <2>1,  SMT  DEFS InductiveInvariant, i1,i0,w1, typeInt, pre,maximum
     <2>3. i1'
     BY <2>2,SMT  DEFS InductiveInvariant, i1,i0,w1, typeInt, pre,maximum         
     <2>. QED
     BY <1>a, <2>1,<2>2,<2>3, SMT DEFS InductiveInvariant, i1,i0,w1, typeInt, pre,maximum
<1>b. CASE a  >=  b
     <2>1.  pc="w1" /\ a >= b /\ r'=a /\ pc' = "Done" /\ UNCHANGED << a, b>>
     BY <1>b,  SMT  DEFS InductiveInvariant, i1,i0,w1, typeInt, pre,maximum
     <2>2.  pc' = "Done" => r' =maximum(a0,b0)
     BY <1>b, <2>1,  SMT  DEFS InductiveInvariant, i1,i0,w1, typeInt, pre,maximum
     <2>3. i1'
     BY <1>b,<2>1,<2>2,SMT  DEFS InductiveInvariant, i1,i0,w1, typeInt, pre,maximum         
     <2>. QED
     BY <1>b, <2>1,<2>2,<2>3, SMT DEFS InductiveInvariant, i1,i0,w1, typeInt, pre,maximum
<1>2. QED     
  BY  <1>a, <1>b, SMT DEFS InductiveInvariant, i1,i0,w1, typeInt, pre,maximum



THEOREM NextProperty == 
ASSUME InductiveInvariant, [Next]_<< rs, re, input, cur, ce, cs, pc >>
PROVE InductiveInvariant'

<1> SUFFICES ASSUME InductiveInvariant /\ [Next]_<< rs, re, input, cur, ce, cs, pc >>
PROVE  InductiveInvariant'
OBVIOUS
<1>1. ASSUME InductiveInvariant, w
PROVE  InductiveInvariant'
BY Zenon, SMT, PTL DEF InductiveInvariant,w
<1>. QED
BY <1>1,Zenon, SMT,PTL  DEF InductiveInvariant, pre




THEOREM Correctness == Spec => []InductiveInvariant
<1>1. Init => InductiveInvariant
  BY Assumption DEF Init, InductiveInvariant,  pre
<1>2. InductiveInvariant /\ [Next]_vars => InductiveInvariant'
  BY PTL DEF InductiveInvariant, Next, vars, 
         w
<1>. QED  BY <1>1, <1>2, PTL  DEF Spec



==============================