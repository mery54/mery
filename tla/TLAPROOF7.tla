------------- MODULE TLAPROOF7 --------------------------
EXTENDS Naturals, Integers,TLC,TLAPS
---------------------------------------------------------
------------------------------- MODULE malgtd1ex12 -------------------------------
(* computing the maximum value of an array f *)
EXTENDS Naturals, TLC,Integers
CONSTANTS undef,n0,f0,i0,m0,min,max
--------------------------------
VARIABLES n,f,m,i,pc
--------------------------------
(* Auxiliary defintions *)
(* an exampe for an array *)
def0 == [j \in 0..n0-1 |-> n0-j]
(* defintion of the range of a function *)
ran(g) == { u  \in Nat : ( \E j \in DOMAIN g : g[j]=u) }
(* defintion of the restriction of a function *)
Rest(g,l) == [k \in 0..l |-> g[k]]
(* precondition *)
pre == 
    /\ n0 \in Nat /\ n0 # 0  
    /\ f0 = def0 
    /\ i0 \in Int /\ m0 \in Int 
pre1 == f=f0 /\ n=n0 /\ pre
(* Integers for your computer *)
zinf == min..max
(* Naturals  for your computer *)
ninf == 0..max  
--------------------------------
(* assuming precondition  over initial values of variables *)
ASSUME pre
--------------------------------
(* Initialisaton for tyhe TLA model *)
Init == /\ i = i0
        /\ m = m0
        /\ f=f0
        /\ n=n0
        /\ pc = "l0"
---------------------------------- 
(* actions for transition *)        
l0l1 == /\ pc = "l0" 
        /\ m' = f[0]
        /\ pc'= "l1"
        /\ UNCHANGED <<n,f,i>>
        
l1l2 == /\ pc = "l1"
        /\ i' = 1
        /\ pc'= "l2"  
        /\ UNCHANGED <<n,f,m>>
                         
l2l3 == /\ pc = "l2"
        /\ i < n
        /\ pc'= "l3"
        /\ UNCHANGED <<n,f,m,i>>
   
           
l2l8 == /\ pc = "l2"
        /\ (i \geq n)
        /\ m' = m
        /\ i' = i
        /\ pc'= "l8"
        /\ UNCHANGED <<n,f>>
          
l3l4 == /\ pc = "l3"
        /\ f[i] > m
        /\ m' = m
        /\ i' = i
        /\ pc'= "l4"
        /\ UNCHANGED <<n,f>>
                  
l3l6 == /\ pc = "l3"
        /\ (f[i] \leq m)
        /\ m' = m
        /\ i' = i
        /\ pc'= "l6"
        /\ UNCHANGED <<n,f>>
   
l4l5 == /\ pc = "l4"
        /\ m' = f[i]
        /\ i' = i
        /\ pc'= "l5"
        /\ UNCHANGED <<n,f>>
        
l5l6 == /\ pc = "l5"
        /\ m' = m
        /\ i' = i
        /\ pc'= "l6"
        /\ UNCHANGED <<n,f>>
           
l6l7 == /\ pc = "l6"
        /\ m' = m
        /\ i' = i + 1
        /\ pc'= "l7"
       /\ UNCHANGED <<n,f>>
                   
l7l3 == /\ pc = "l7"
        /\ i < n 
        /\ m' = m
        /\ i' = i
        /\ pc'= "l3"
        /\ UNCHANGED <<n,f>>
    
 l7l8 == 
        /\ pc = "l7"
        /\ i \geq n 
        /\ m' = m
        /\ i' = i
        /\ pc'= "l8"
        /\ UNCHANGED <<n,f>>
--------------------------------
(* Next relatioon over  values variables *)   
 Next == \/ l0l1
        \/ l1l2
        \/ l2l3
        \/ l2l8
        \/ l3l4
        \/ l3l6
        \/ l4l5
        \/ l5l6
        \/ l6l7
        \/ l7l3
        \/ l7l8
        \/ UNCHANGED <<n,m,i,f,pc>>
 
  Dl0l1 ==  0\leq 0 /\ 0 \leq n0-1
  Dl1l2 == 1 \in zinf
inv ==
   /\ pc \in {"l0","l1","l2","l3","l4","l5","l6","l7","l8"}
   /\ n \in Int /\ f = def0 /\ i \in Int /\ m \in Int 
   /\ pc="l0" =>   f=f0 /\ n=n0 /\ m=m0 /\ i = i0/\ pre
   /\ pc="l1" =>  f=f0 /\ n=n0 /\ m=f[0] /\ i = i0 /\ pre
   /\ pc ="l2" =>  i=1 /\  m \in Nat /\ (m \in ran(Rest(f,i-1))) /\ (\A k  \in 0..i-1: f[k] \leq m) /\ pre1
   /\ pc="l3" =>     (i \in 1..n-1) /\  m \in Nat /\ (m \in ran(Rest(f,i-1))) /\ (\A k  \in 0..i-1: f[k] \leq m) /\ pre1
   /\ pc="l4" =>    f[i] > m /\ (i \in 1..n-1) /\  m \in Nat /\ (m \in ran(Rest(f,i-1))) /\ (\A k  \in 0..i-1: f[k] \leq m) /\ pre1
   /\ pc="l5"  =>   f[i] > m /\ (i \in 1..n-1) /\  m \in Nat /\ (m \in ran(Rest(f,i))) /\ (\A k  \in 0..i: f[k] \leq m) /\ pre1
   /\ pc="l6" =>    (i \in 1..n-1) /\  m \in Nat /\ (m \in ran(Rest(f,i))) /\ (\A k  \in 0..i: f[k] \leq m) /\ pre1
   /\ pc="l7" =>    (i \in 1..n) /\  m \in Nat /\ (m \in ran(Rest(f,i-1))) /\ (\A k  \in 0..i-1: f[k] \leq m) /\ pre1
   /\ pc="l8" =>   i=n /\  m \in Nat /\ (m \in ran(Rest(f,i-1))) /\ (\A k  \in 0..i-1: f[k] \leq m) /\ pre1

partialcorrectness == pc="l8" => m \in Nat /\ (m \in ran(Rest(f,n-1))) /\ (\A k  \in 0..n-1: f[k] \leq m) /\ pre1   
  
runtimeerrors ==  m \in zinf /\ i \in zinf /\ n \in zinf

safe ==  inv  /\ runtimeerrors  /\ partialcorrectness 

ASSUME pre
---------------------------------------------------------
vars == <<pc,n,f,m,i>>
Spec == Init/\  [] [Next]_vars
---------------------------------------------------------
InductiveInvariant ==  inv

---------------------------------------------------------
ASSUME Assumption == pre

THEOREM InitProperty == Init => InductiveInvariant
<1> SUFFICES ASSUME Init
PROVE  InductiveInvariant
OBVIOUS
<1>1. n=n0 BY Assumption  DEF Init
<1>2. f=f0 BY Assumption  DEF Init
<1>3. m=m0 BY Assumption  DEF Init
<1>4. i=i0 BY Assumption  DEF Init
<1>5. pc="l0" BY Assumption  DEF Init
<1>6.  pre  BY Assumption  DEF Init
<1>. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6   DEF InductiveInvariant,pre,def0

================================
