--------------- MODULE DieHard ---------------
EXTENDS Integers
VARIABLES big, small

Init ==  /\ big = 0 
         /\ small = 0

TypeOK ==  /\ small \in 0..3
          /\ big \in 0..5
          
FillSmall == /\ big'= big 
             /\ small'= 3
            
FillBig == /\ small'= small 
           /\ big'= 5

EmptySmall == /\ big'= big 
              /\ small'= 0

EmptyBig == /\ small'= small 
            /\ big'= 0
             
BigtoSmall == IF big+small =< 3 
                 THEN /\ big'=0
                      /\ small'=small+big
                 ELSE /\ big'=big-(3-small)
                      /\ small'=3

SmalltoBig == IF big+small =< 5 
                 THEN /\ small'=0
                      /\ big'=small+big
                 ELSE /\ small'=small-(5-big)
                      /\ big'=5
                   
Next == \/ FillSmall
        \/ FillBig
        \/ EmptySmall
        \/ EmptyBig
        \/ BigtoSmall
        \/ SmalltoBig
====================================================