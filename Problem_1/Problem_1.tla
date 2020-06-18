----------------------------- MODULE Problem_1 -----------------------------
(*
    void producer () {
        while (true) {
            /* W: Working */
            produce_item();
            if (count==N) /*BS: Before-Sleeping */
                sleep(); /*S: Sleeping" */
            /*AS: After-Sleeping */
            insert_item();
            count = count + 1;
            /*AC: After-Changing */
            if (count==1) /*BW: Before-Wakeup */
                wakeup(consumer);
    }
*)

(*
    void consumer() {
        while(true) {
            if (count==0) /*BS: Before-Sleeping */
                sleep(); /*S: Sleeping" */
            /*AS: After-Sleeping */
            remove_item();
            count = count-1;
            /*AC: After-Changing */
            if (count == N - 1) /*BW: Before-Wakeup */
                wakeup(producer);
            /*W: Working */
            consume_item();
        }
    }
*)
EXTENDS Integers

CONSTANT N
VARIABLE Producer
VARIABLE Consumer
VARIABLE count
Init == 
    /\ Producer = "W"
    /\ Consumer = "W"
    /\ count = 0

TypeOK ==
    /\ Producer \in {"W", "BS", "S", "AS", "AC", "BW"}
    /\ Consumer \in {"W", "BS", "S", "AS", "AC", "BW"}


(*********************Producer Behaviour*********************)
Producer_to_BS == 
    /\ Producer = "W"
    /\ count = N
    /\ Producer' = "BS"
    /\ Consumer' = Consumer
    /\ count' = count

Producer_to_S == 
    /\ Producer = "BS"
    /\ Producer' = "S"
    /\ Consumer' = Consumer
    /\ count' = count

Producer_to_AS ==
    \/ /\ Producer = "W"
       /\ count # N
       /\ Producer' = "AS"
       /\ Consumer' = Consumer
       /\ count' = count
    \/ /\ Consumer = "BW"
       \* Be waken up
       /\ Producer' = IF Producer = "S" 
                      THEN "AS"
                      ELSE Producer
       /\ Consumer' = "W"
       /\ count' = count

Producer_to_AC == 
    /\ Producer = "AS"
    /\ Producer' = "AC"
    /\ Consumer' = Consumer
    /\ count' = count + 1

Producer_to_BW == 
    /\ Producer = "AC"
    /\ count = 1
    /\ Producer' = "BW"
    /\ Consumer' = Consumer
    /\ count' = count

\* wakeup was already considered in Consumer_to_AS
Producer_to_W == 
    /\ Producer = "AC"
    /\ count # 1
    /\ Producer' = "W"
    /\ Consumer' = Consumer
    /\ count' = count
    
(*********************Consumer Behaviour*********************)
Consumer_to_BS ==
    /\ Consumer = "W"
    /\ count = 0
    /\ Consumer' = "BS"
    /\ Producer' = Producer
    /\ count' = count

Consumer_to_S ==
    /\ Consumer = "BS"
    /\ Consumer' = "S"
    /\ Producer' = Producer
    /\ count' = count

Consumer_to_AS ==
   \/ /\ Consumer = "W"
      /\ count # 0
      /\ Consumer' = "AS"
      /\ Producer' = Producer
      /\ count' = count
   \/ /\ Producer = "BW"
       \* Be waken up
      /\ Consumer' = IF Consumer = "S" 
                     THEN "AS"
                     ELSE Consumer
      /\ Producer' = "W"
      /\ count' = count

Consumer_to_AC ==
    /\ Consumer = "AS"
    /\ Consumer' = "AC"
    /\ Producer' = Producer
    /\ count' = count - 1

Consumer_to_BW ==
    /\ Consumer = "AC"
    /\ count = N - 1
    /\ Consumer' = "BW"
    /\ Producer' = Producer
    /\ count' = count

\* wakeup was already considered in Producer_to_AS
Consumer_to_W ==
    /\ Consumer = "AC"
    /\ count # N - 1
    /\ Consumer' = "W"
    /\ Producer' = Producer
    /\ count' = count

Next ==
    \/ Producer_to_BS
    \/ Producer_to_S
    \/ Producer_to_AS
    \/ Producer_to_AC
    \/ Producer_to_BW
    \/ Producer_to_W
    \/ Consumer_to_BS
    \/ Consumer_to_S
    \/ Consumer_to_AS
    \/ Consumer_to_AC
    \/ Consumer_to_BW
    \/ Consumer_to_W
    
    
Deadlock == 
    /\ Producer = "S"
    /\ Consumer = "S"

NoDeadlock ==
    ~ Deadlock

NoException1 == 
    count >= 0

NoException2==
    count <= N

=============================================================================
\* Modification History
\* Last modified Fri Jun 19 04:25:28 CST 2020 by youngster
\* Created Wed Jun 17 13:24:42 CST 2020 by youngster







    
    