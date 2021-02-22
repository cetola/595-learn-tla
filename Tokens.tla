------------------------------- MODULE Tokens -------------------------------
EXTENDS Reals
(***************************************************************************)
(* The two requestors and one manager. T is the max number of tokens       *)
(***************************************************************************)
CONSTANT T, R1, R2
VARIABLES req1, req2, manager

(*************************************************************************)
(* The type-correctness invariant                                        *)
(*************************************************************************)
TypeInvariant == 
    /\ req1 <= T /\ req1 <= R1
    /\ req2 <= T /\ req2 <= R2
    /\ manager <= T
    
(*************************************************************************)
(* The manager starts with the maximum allowed tokens, others 0          *)
(*************************************************************************)
Init ==
  /\ req1 = 0
  /\ req2 = 0
  /\ manager = T
  
(*******************************************************************************)
(* These are the conditions under which we can allocate tokens to a requestor  *)
(*******************************************************************************)
ServiceReq1 == (manager - (R1-req1)) >= 0
ServiceReq2 == (manager - (R2-req2)) >= 0
 
(*******************************************************************************)
(* Service a request and reset requests when filled                            *)
(*******************************************************************************)                
ServiceReq == 
    /\ IF ServiceReq1 THEN req1' = req1 + 1 /\ manager' = manager - 1 ELSE req1' = req1
    /\ IF ServiceReq2 THEN req2' = req2 + 1 /\ manager' = manager - 1 ELSE req2' = req2
    
RequestFilled ==
    \/ IF req1 = R1 THEN manager' = manager + R1 /\ req1' = 0 /\ req2' = req2 ELSE FALSE
    \/ IF req2 = R2 THEN manager' = manager + R2 /\ req1' = req1 /\ req2' = 0 ELSE FALSE
    

(*******************************************************************************)
(* Either a request is filled or we service a request                          *)
(*******************************************************************************)  
Next == IF ~ RequestFilled THEN ServiceReq ELSE TRUE

Spec == Init /\ [][Next]_<<req1, req2, manager>>
=============================================================================
\* Modification History
\* Last modified Sat Dec 05 20:09:59 PST 2020 by stephano
\* Created Mon Nov 23 11:40:35 PST 2020 by stephano
