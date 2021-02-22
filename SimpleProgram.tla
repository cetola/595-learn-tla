--------------------------- MODULE SimpleProgram ---------------------------
EXTENDS Integers
VARIABLES i, pc

Init == (i = 0) /\ (pc = "start")

Next == \/ /\ pc = "start"
           /\ pc' = "middle"
           /\ i' \in 1..1000
        \/ /\ pc = "middle"
           /\ pc' = "done"
           /\ i' = i + 1
=============================================================================
\* Modification History
\* Last modified Thu Nov 19 20:37:27 PST 2020 by stephano
\* Created Thu Nov 19 20:27:36 PST 2020 by stephano
