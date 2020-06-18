-------------------------- MODULE HW_Spining_Lock ----------------------------
EXTENDS Integers

CONSTANT  r1, r2       \* threads
VARIABLE Threads      
VARIABLE States        \* State[thrd] is the state of a thread.
VARIABLE turn
-----------------------------------------------------------------------------
TypeOK == 
  (*************************************************************************)
  (* The type-correctness invariant                                        *)
  (*************************************************************************)
  /\ States \in [Threads -> {"critical", "finish-critical", "non-critical"}]
  /\ turn \in 0..1
  
     
Init ==   Threads = {r1, r2}
            /\ States = [r \in Threads |-> "non-critical"]
            /\ turn = 0
  (*************************************************************************)
  (* The initial predicate.                                                *)
  (*************************************************************************)

-----------------------------------------------------------------------------
(***************************************************************************)
(* the actions that may be performed                                       *)
(***************************************************************************)
ChangeTurn == \/ /\ turn = 0
                 /\ turn'= 1
              \/ /\ turn = 1
                 /\ turn'= 0
\*ChangeTurn == turn' = ~ turn

IntoCritical(r) == /\ IF r = r1 THEN turn = 0 ELSE turn = 1
                   /\ States[r] = "non-critical"
                   /\ States' = [States EXCEPT ![r] = "critical"]
                   /\ turn' = turn
                   /\ Threads' = Threads

ChangeT(r) == /\ States[r] = "critical"
              /\ ChangeTurn
              /\ States' = [States EXCEPT ![r] = "finish-critical"]
              /\ Threads' = Threads

OffCritical(r) == /\ States[r] = "finish-critical"
                  /\ States' = [States EXCEPT ![r] = "non-critical"]
                  /\ turn' = turn
                  /\ Threads' = Threads
                  

  (*************************************************************************)
  (* The next-state action.                                                *)
  (*************************************************************************)
Next == \E r \in Threads: IntoCritical(r) \/ ChangeT(r) \/ OffCritical(r)

-----------------------------------------------------------------------------
  (*************************************************************************)
  (* The invariant                                                         *)
  (*************************************************************************)
Consistent ==  
  \A t1, t2 \in Threads: ~ /\ States[r1] = "critical"
                           /\ States[r2] = "critical"
  (*************************************************************************)
  ==========================================================================
