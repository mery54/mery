---------- MODULE TLAPROOFODDEVEN  ---------
EXTENDS TLAPROOFDOMAIN
-------------------------------
CONSTANTS n
-------------------------------
pre(u) == u >= 0

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
                      THEN /\ PL}
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


---------------------------------------------------------------

i1 == cur \in 0..n  /\ input = n  /\ rs \in Int  /\  pc \in {"w","Done"}
i2 == (pc = "w") => (cs = s[cur])
i3 ==   (pc = "Done") =>  (rs=s[n])
i4 == (pc = "Done") =>  (re=es[n]) 
InductiveInvariant ==   i1 /\ i2 /\ i3 /\ i4


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


<1>1. cur \in 0..n  BY  SMT  DEFS InductiveInvariant,w,pre
<1>a. CASE cur \in 0..n-1
     <2>1.  pc="w"   /\  UNCHANGED << rs, re, input >>
     BY <1>a,  SMT  DEFS InductiveInvariant, i1,i2,i4,i3,w, pre
     <2>2. input = n /\ rs \in Int  /\  pc \in {"w","Done"}
     BY <1>a,  SMT  DEFS InductiveInvariant, i1,i2,i4,i3,w, pre
     <2>3.pc'=pc /\ ( (pc' = "w") => (cs' = s[cur']))
     BY <1>a,  SMT  DEFS InductiveInvariant, i1,i2,i4,i3,w, pre     
     <2>10. InductiveInvariant'
     BY <1>a, <2>1, SMT  DEFS InductiveInvariant, i1,i2,i3,i4,w, pre        
     <2>11. QED
     BY <1>a, <2>1,<2>2, SMT DEFS InductiveInvariant,w, pre
<1>b. CASE cur = n
     <2>1.  pc="w" /\ cur < n   /\ pc' = "Done"/\ UNCHANGED << rs, re, input >>
     BY <1>a,  SMT  DEFS InductiveInvariant, i1,i2,i3,i4,w, pre
     <2>2. InductiveInvariant'
     BY <2>2,SMT  DEFS InductiveInvariant, i1,i2,i3,i4,w,pre       
     <2>3. QED
     BY <1>a, <2>1,<2>2, SMT DEFS InductiveInvariant,w, pre
<1>2. QED     
  BY  <1>a, <1>b, SMT DEFS InductiveInvariant,w, pre



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

======================================================
 
