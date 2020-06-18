----------------------------- MODULE Problem_2 -----------------------------
\* Author: Z. Yang from SJTU

(*
    semaphore mutex=1, empty=N, full=0;
    
    void producer () {
        while (true) {
            /* U2: Up_2 */
            down(&empty); /* S1: Sleep_1 */
                /* D1: Down_1 */
                down(&mutex); /* S2: Sleep_2 */
                    /* D2: Down_2 */
                up(&mutex); 
                /* U1: Up_1 */
            up(&full);
            /* U2: Up_2 */
        }
    }
    
    void consumer() {
        while(true) {
            /* U2: Up_2 */
            down(&full); /* S1: Sleep_1 */
                /* D1: Down_1 */
                down(&mutex); /* S2: Sleep_2 */
                    /* D2: Down_2 */
                up(&mutex); 
                /* U1: Up_1 */
            up(&empty); 
            /* U2: Up_2 */
        }
    }
*)

EXTENDS Integers, Semaphore, FiniteSets
CONSTANT N
CONSTANT Producers, Consumers
VARIABLE ProState, ConState
VARIABLE mutex, empty, full

ThreadTypes == {"Producer", "Consumer"}
StateTypes == {"U1", "U2", "S1", "S2", "D1", "D2"}


Init ==
    /\ mutex = [value |-> 1, sleep |-> 0]
    /\ empty = [value |-> N, sleep |-> 0]
    /\ full = [value |-> 0, sleep |-> 0]
    /\ ProState = [x \in Producers |-> [type |-> "Producer", state |-> "U2"]]
    /\ ConState = [x \in Consumers |-> [type |-> "Consumer", state |-> "U2"]]

State(x) == IF x \in Producers THEN ProState[x] ELSE ConState[x]
threads == Producers \cup Consumers

\* Cardinality(S) == number of elements in set S
TypeOK == 
    /\ \A x \in threads: State(x).state \in StateTypes
    /\ \A x \in threads: State(x).type \in ThreadTypes
    /\ mutex.value \in 0..1
    /\ mutex.sleep \in 0..Cardinality(threads)-1
    /\ empty.value \in 0..N
    /\ empty.sleep \in 0..Cardinality(threads)-1
    /\ full.value \in 0..N
    /\ full.sleep \in 0..Cardinality(threads)-1
    
Deadlock ==
    \A x \in threads: State(x).state \in {"S1", "S2"}

NoDeadlock ==
    ~ Deadlock

\* From U2 to D1, without going to sleep    
U2_to_D1(t) ==
    \/ /\ State(t).type = "Producer"
       /\ State(t).state = "U2"
       /\ down(empty)
       /\ ProState' = [ProState EXCEPT ![t] = [type |-> "Producer", state |-> "D1"]]
       /\ ConState' = ConState
       /\ UNCHANGED<<mutex, full>>
    \/ /\ State(t).type = "Consumer"
       /\ State(t).state = "U2"
       /\ down(full)
       /\ ConState' = [ConState EXCEPT ![t] = [type |-> "Consumer", state |-> "D1"]]
       /\ ProState' = ProState
       /\ UNCHANGED<<mutex, empty>>
       
\* From U2 to S1, going to sleep
U2_to_S1(t) ==
    \/ /\ State(t).type = "Producer"
       /\ State(t).state = "U2"
       /\ sleep(empty)
       /\ ProState' = [ProState EXCEPT ![t] = [type |-> "Producer", state |-> "S1"]]
       /\ ConState' = ConState
       /\ UNCHANGED<<mutex, full>>
    \/ /\ State(t).type = "Consumer"
       /\ State(t).state = "U2"
       /\ sleep(full)
       /\ ConState' = [ConState EXCEPT ![t] = [type |-> "Consumer", state |-> "S1"]]
       /\ ProState' = ProState
       /\ UNCHANGED<<mutex, empty>>
       
       
S1_to_D1(t) ==
    \* Producer was waken up from empty
    \/ /\ State(t).type = "Producer"
       /\ State(t).state = "S1"
       /\ (\E t1 \in Consumers: 
            /\ State(t1).state = "U1"
            /\ ConState' = [ConState EXCEPT ![t1] = [type |-> "Consumer", state |-> "U2"]]
            /\ wake(empty))
       /\ ProState' = [ProState EXCEPT ![t] = [type |-> "Producer", state |-> "D1"]]
       /\ UNCHANGED<<mutex, full>>
    \* Consumer was waken up from full 
    \/ /\ State(t).type = "Consumer"
       /\ State(t).state = "S1"
       /\ (\E t1 \in Producers: 
            /\ State(t1).state = "U1"
            /\ ProState' = [ProState EXCEPT ![t1] = [type |-> "Producer", state |-> "U2"]]
            /\ wake(full))
       /\ ConState' = [ConState EXCEPT ![t] = [type |-> "Consumer", state |-> "D1"]]
       /\ UNCHANGED<<mutex, empty>>

\* From D1 to D2, without going to sleep
D1_to_D2(t) ==
    \/ /\ State(t).state = "D1"
       /\ down(mutex)
       /\ IF t \in Producers 
          THEN /\ ProState' = [ProState EXCEPT ![t] = [type |-> "Producer", state |-> "D2"]]
               /\ ConState' = ConState
          ELSE /\ ConState' = [ConState EXCEPT ![t] = [type |-> "Consumer", state |-> "D2"]]
               /\ ProState' = ProState 
       /\ UNCHANGED<<full, empty>>

\* From D1 to S2, going to sleep
D1_to_S2(t) ==
    \/ /\ State(t).state = "D1"
       /\ sleep(mutex)
       /\ IF t \in Producers 
          THEN /\ ProState' = [ProState EXCEPT ![t] = [type |-> "Producer", state |-> "S2"]]
               /\ ConState' = ConState
          ELSE /\ ConState' = [ConState EXCEPT ![t] = [type |-> "Consumer", state |-> "S2"]]
               /\ ProState' = ProState 
       /\ UNCHANGED<<full, empty>>


\* From S2 to D2
\* Be waken up from mutex
S2_to_D2(t) ==
    \* Producer was waken up from mutex
    \/ /\ State(t).type = "Producer"
       /\ State(t).state = "S2"
       /\ ( \* Waken by a Consumer 
            \/ /\ (\E t1 \in Consumers: 
                  /\ State(t1).state = "D2"
                  /\ ConState' = [ConState EXCEPT ![t1] = [type |-> "Consumer", state |-> "U1"]]
                  /\ wake(mutex))
               /\ ProState' = [ProState EXCEPT ![t] = [type |-> "Producer", state |-> "D2"]]
            \* Waken by another Producer
            \/ /\ (\E t1 \in Producers: 
                  /\ State(t1).state = "D2"
                  /\ ProState' = 
                     [ProState EXCEPT ![t1] = [type |-> "Producer", state |-> "U1"],
                                      ![t] =  [type |-> "Producer", state |-> "D2"]]
                  /\ wake(mutex))
             /\ ConState' = ConState
          )
       /\ UNCHANGED<<empty, full>>
    \* Consumer was waken up from mutex
    \/ /\ State(t).type = "Consumer"
       /\ State(t).state = "S2"
       /\ ( \* Waken by a producer
            \/ /\ (\E t1 \in Producers: 
                  /\ State(t1).state = "D2"
                  /\ ProState' = [ProState EXCEPT ![t1] = [type |-> "Producer", state |-> "U1"]]
                  /\ wake(mutex))
               /\ ConState' = [ConState EXCEPT ![t] = [type |-> "Consumer", state |-> "D2"]]
            \* Waken by another Consumer
            \/ /\ (\E t1 \in Consumers: 
                  /\ State(t1).state = "D2"
                  /\ ConState' = 
                     [ConState EXCEPT ![t1] = [type |-> "Consumer", state |-> "U1"],
                                      ![t] =  [type |-> "Consumer", state |-> "D2"]]
                  /\ wake(mutex))
               /\ ProState' = ProState
          )
       /\ UNCHANGED<<empty, full>>


\* From D2 to U1
\* up(&mutex) without waking up
D2_to_U1(t) ==
    \/ /\ State(t).state = "D2"
       /\ up(mutex)
       /\ IF t \in Producers 
          THEN /\ ProState' = [ProState EXCEPT ![t] = [type |-> "Producer", state |-> "U1"]]
               /\ ConState' = ConState
          ELSE /\ ConState' = [ConState EXCEPT ![t] = [type |-> "Consumer", state |-> "U1"]]
               /\ ProState' = ProState 
       /\ UNCHANGED<<full, empty>>
       
       
\* from U1 to U2
\* up(&full) without waking up, as a Producer
\* up(&empty) without waking up, as a Consumer
U1_to_U2(t) ==
    \/ /\ State(t).type = "Producer"
       /\ State(t).state = "U1"
       /\ up(full)
       /\ ProState' = [ProState EXCEPT ![t] = [type |-> "Producer", state |-> "U2"]]
       /\ ConState' = ConState
       /\ UNCHANGED<<mutex, empty>>
    \/ /\ State(t).type = "Consumer"
       /\ State(t).state = "U1"
       /\ up(empty)
       /\ ConState' = [ConState EXCEPT ![t] = [type |-> "Consumer", state |-> "U2"]]
       /\ ProState' = ProState
       /\ UNCHANGED<<mutex, full>>


(*
        U2
        |  \
        |   S1
        |  /
        D1 
        |  \
        |   S2
        |  /
        D2
        |
        U1 --- U2
*)
Next ==
    \E t \in Producers \cup Consumers:
        \/ U2_to_D1(t)
        \/ U2_to_S1(t)
        \/ S1_to_D1(t)
        \/ D1_to_D2(t)
        \/ D1_to_S2(t)
        \/ S2_to_D2(t)
        \/ D2_to_U1(t)
        \/ U1_to_U2(t)


=============================================================================
\* Modification History
\* Last modified Fri Jun 19 04:22:22 CST 2020 by youngster
\* Created Thu Jun 18 17:54:32 CST 2020 by youngster
