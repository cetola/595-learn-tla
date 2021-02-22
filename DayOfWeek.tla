----------------------------- MODULE DayOfWeek -----------------------------
EXTENDS Naturals
VARIABLE day, state

DaySequence == <<"Sunday", "Monday", "Tuesday", "Wednesday", "Thursday", "Friday", "Saturday">>
DaySequenceLen == 7

TypeInvariant == /\ state \in (1..DaySequenceLen)
                 /\ day \in {"Sunday", "Monday", "Tuesday", "Wednesday", "Thursday", "Friday", "Saturday"}
Init == /\ day = DaySequence[1]
        /\ state=1
Next == LET nextState == IF state # DaySequenceLen THEN state+1 ELSE 1
        IN   /\ state' = nextState
             /\ day' = DaySequence[nextState]
             
Spec == Init /\ [][Next]_<<day, state>>
=============================================================================
\* Modification History
\* Last modified Sat Dec 05 16:27:22 PST 2020 by stephano
\* Created Fri Nov 20 16:38:32 PST 2020 by stephano
