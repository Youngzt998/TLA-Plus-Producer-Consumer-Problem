----------------------------- MODULE Problem_2 -----------------------------

EXTENDS Integers, Semaphore
CONSTANT N
VARIABLE threads
VARIABLE mutex, empty, full

ThreadType == {"Producer", "Consumer"}

Init ==
    /\ mutex = [value |-> 1, sleep |-> 0]
    /\ empty = [value |-> N, sleep |-> 0]
    /\ full = [value |-> 0, sleep |-> 0]
    /\ threads = {[type |-> "Producer", state |-> "Consumer"]}


U2_to_D1(t) ==
    \/ /\ t.type = "Producer"
       /\ t.state = "U2"
       /\ down(empty)
       /\ t' = [type |-> "Producer", state |-> "D1"]
       /\ UNCHANGED<<mutex, full>>
    \/ /\ t.type = "Consumer"
       /\ t.state = "U2"
       /\ down(full)
       /\ t' = [t EXCEPT !.state = "D1"]
       /\ UNCHANGED<<mutex, empty>>
       
U2_to_S1(t) ==
    \/ /\ t.type = "Producer"
       /\ t.state = "U2"
       /\ sleep(empty)
       /\ t' = [t EXCEPT !.state = "S1"]
       /\ UNCHANGED<<mutex, full>>
    \/ /\ t.type = "Consumer"
       /\ t.state = "U2"
       /\ sleep(full)
       /\ t' = [t EXCEPT !.state = "S1"]
       /\ UNCHANGED<<mutex, empty>>
       
       
\* Producer was waken up from empty
\* Consumer was waken up from full 
S1_to_D1(t) ==
    \/ /\ t.type = "Producer"
       /\ t.state = "S1"
       /\ (\E t1 \in threads: 
            /\ t1.type = "Consumer"
            /\ t1.state = "U1"
            /\ t1' = [t EXCEPT !.state = "U2"]
            /\ wake(empty))
       /\ t' = [t EXCEPT !.state = "D1"]
       /\ UNCHANGED<<mutex, full>>
    \/ /\ t.type = "Consumer"
       /\ t.state = "S1"
       /\ (\E t1 \in threads: 
            /\ t1.type = "Producer"
            /\ t1.state = "U1"
            /\ t1' = [t EXCEPT !.state = "U2"]
            /\ wake(full))
       /\ t' = [t EXCEPT !.state = "D1"]
       /\ UNCHANGED<<mutex, empty>>

D1_to_D2(t) ==
    \/ /\ t.state = "D1"
       /\ down(mutex)
       /\ t' = [t EXCEPT !.state = "D2"]
       /\ UNCHANGED<<full, empty>>

       
D1_to_S2(t) ==
    \/ /\ t.state = "D1"
       /\ sleep(mutex)
       /\ t' = [t EXCEPT !.state = "S2"]
       /\ UNCHANGED<<full, empty>>


\* Producer was waken up from mutex
S2_to_D2(t) ==
    \/ /\ t.type = "Producer"
       /\ t.state = "S2"
       /\ (\E t1 \in threads: 
            /\ t1.type = "Consumer"
            /\ t1.state = "D2"
            /\ t1' = [t EXCEPT !.state = "U1"]
            /\ wake(mutex))
       /\ t' = [t EXCEPT !.state = "D2"]
       /\ UNCHANGED<<full, empty>>
    \/ /\ t.type = "Consumer"
       /\ t.state = "S2"
       /\ (\E t1 \in threads: 
            /\ t1.type = "Producer"
            /\ t1.state = "D2"
            /\ t1' = [t EXCEPT !.state = "U1"]
            /\ wake(mutex))
       /\ t' = [t EXCEPT !.state = "D2"]
       /\ UNCHANGED<<full, empty>>

\* up(&mutex) without waking up
D2_to_U1(t) ==
    /\ t.state = "D2"
    /\ up(mutex)
    /\ t' = [t EXCEPT !.state = "U1"]
    /\ UNCHANGED<<full, empty>>

\* up(&full) without waking up [Producer]
\* up(&empty) without waking up [Consumer]
U1_to_U2(t) ==
    \/ /\t.type = "Producer"
       /\ t.state = "U1"
       /\ up(full)
       /\ t' = [t EXCEPT !.state = "U2"]
       /\ UNCHANGED<<mutex, empty>>
    \/ /\t.type = "Consumer"
       /\ t.state = "U1"
       /\ up(empty)
       /\ t' = [t EXCEPT !.state = "U2"]
       /\ UNCHANGED<<mutex, full>>


Next ==
    \E t \in threads:
        \/ U2_to_D1(t)
        \/ U2_to_S1(t)
        \/ S1_to_D1(t)
        \/ D1_to_D2(t)
        \/ D1_to_S2(t)
        \/ S2_to_D2(t)
        \/ D2_to_U1(t)
        \/ U1_to_U2(t)

\*        \/ U2_to_D1(Pro)
\*        \/ U2_to_S1(Pro)
\*        \/ S1_to_D1(Pro)
\*        \/ D1_to_D2(Pro)
\*        \/ D1_to_S2(Pro)
\*        \/ S2_to_D2(Pro)
\*        \/ D2_to_U1(Pro)
\*        \/ U1_to_U2(Pro)
\*        \/ U2_to_D1(Cons)
\*        \/ U2_to_S1(Cons)
\*        \/ S1_to_D1(Cons)
\*        \/ D1_to_D2(Cons)
\*        \/ D1_to_S2(Cons)
\*        \/ S2_to_D2(Cons)
\*        \/ D2_to_U1(Cons)
\*        \/ U1_to_U2(Cons)


=============================================================================
\* Modification History
\* Last modified Fri Jun 19 00:26:17 CST 2020 by youngster
\* Created Thu Jun 18 17:54:32 CST 2020 by youngster
