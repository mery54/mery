----------MODULE TLAPROOFODDEVEN---------
EXTENDS Naturals,TLAPS
p == 8
(*
--algorithm oddeven {
variables  rs=0,re=0,input=p,cur=0,ce=0,cs=0;
	   { w:while (cur # p) {
	   if (cur % 2 # 0) {cs := cs+cur+1;ce := ce+cur+1;cur := cur+1}
	   else { cs := cs+cur+1;ce :=ce;cur := cur+1;};
	   };
	   }
	   }
*)
\* BEGIN TRANSLATION (chksum(pcal) = "d13c8e98" /\ chksum(tla) = "3d33e22b")
VARIABLES rs, re, input, cur, ce, cs, pc

vars == << rs, re, input, cur, ce, cs, pc >>

Init == (* Global variables *)
        /\ rs = 0
        /\ re = 0
        /\ input = p
        /\ cur = 0
        /\ ce = 0
        /\ cs = 0
        /\ pc = "w"

w == /\ pc = "w"
     /\ IF cur # p
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
--------------------------------------------------

======================================================
 
