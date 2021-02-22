------------------------------- MODULE Bridge -------------------------------
EXTENDS Integers
(***************************************************************************)
(* current number of people on the bridge and direction they entered from  *)
(***************************************************************************)
CONSTANT MAX
VARIABLES west, east, state
stateSeq == <<"entree", "egress">>

  (*************************************************************************)
  (* The type-correctness invariant                                        *)
  (*************************************************************************)
TypeInvariant == 
    /\ ~(east > 0 /\ west > 0)
    /\ state \in {"entree", "egress"}
    
  (*************************************************************************)
  (* Assume no one is on the bridge, switch between east and west          *)
  (*************************************************************************)
Init ==
  /\ state = "entree"
  /\ east = 0
  /\ west = 0
  
  (*******************************************************************************)
  (* We only want to exit or enter the bridge if one of these conditions is true *)
  (*******************************************************************************)
Entree ==   /\ west = 0
            /\ east = 0
        
Egress ==   \/ west = MAX
            \/ east = MAX
   
  (*******************************************************************************)
  (* When one of these conditions is true we need to switch states               *)
  (*******************************************************************************)         
Switch == IF Entree THEN state' = "entree" ELSE
          IF Egress THEN state' = "egress" ELSE state' = state
 
  (*******************************************************************************)
  (* Cross, regardless of direction, by entering 1 at a time. Leave all at once  *)
  (*******************************************************************************)                
Cross(d) == IF d = 0 THEN d' = d + 1 ELSE
   IF (d > 0 /\ d < MAX) THEN d' = d + 1 ELSE d' = 0

  (*******************************************************************************)
  (* We are either crossing west or east, and we always switch when at 0 or MAX  *)
  (*******************************************************************************)  
Next == \/ Cross(west) /\ Switch /\ east' = east
        \/ Cross(east) /\ Switch /\ west' = west

Spec == Init /\ [][Next]_<<east, west, state>>
=============================================================================
\* Modification History
\* Last modified Fri Dec 04 14:48:28 PST 2020 by stephano
\* Created Mon Nov 23 11:40:35 PST 2020 by stephano
