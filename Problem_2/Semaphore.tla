----------------------------- MODULE Semaphore -----------------------------

EXTENDS Integers


(******************** down ********************)
down(x) ==
    \/ /\ x.value > 0
       /\ x' = [x EXCEPT !.value = x.value - 1]

sleep(x)==
    \/ /\ x.value = 0
       /\ x' = [x EXCEPT !.sleep = x.sleep + 1]


(********************* up *********************)
up(x) ==
    \/ /\ x.sleep = 0
       /\ x' = [x EXCEPT !.value = x.value + 1]
       
wake(x) ==
    \/ /\ x.sleep > 0
       /\ x' = [x EXCEPT !.sleep = x.sleep - 1]




=============================================================================
\* Modification History
\* Last modified Thu Jun 18 20:16:42 CST 2020 by youngster
\* Created Thu Jun 18 17:54:32 CST 2020 by youngster