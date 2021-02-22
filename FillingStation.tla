--------------------------- MODULE FillingStation ---------------------------

EXTENDS Integers
(* MAX is 13 *)
CONSTANT MAX
VARIABLES pressure, tank
          
TypeOK == /\ pressure \in 0..5 
          /\ tank \in 0..MAX

(* As we all do every week ~\in 2020, start with the tank at 0 and the pressure at full *)
Init == /\ pressure = 5
        /\ tank = 0


Next == IF tank + pressure =< MAX
               THEN /\ tank'   = tank + pressure
                    /\ pressure' = pressure
               ELSE /\ tank'   = tank
                    /\ pressure' = pressure - 1 
        
Spec == Init /\ [][Next]_<<pressure, tank>>  


=============================================================================
\* Modification History
\* Last modified Wed Dec 09 08:17:22 PST 2020 by stephano
\* Created Tue Dec 08 18:36:03 PST 2020 by stephano
