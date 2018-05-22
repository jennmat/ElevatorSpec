------------------------------ MODULE Elevator ------------------------------
EXTENDS Integers


CONSTANT NumFloors


VARIABLES 
    (* Current position of the elevator car *)
    position,
    (* State of the down button for a given floor  *)
    down,
    (* State of the up button for a given floor *)
    up,
    (* Drop off requesetd for a given floor *)
    destinations
    
Floors == 0..NumFloors-1


vars == <<position, down, up, destinations>>


TypeOK == /\ position >= 0
          /\ position < NumFloors
          /\ down \in [Floors -> BOOLEAN]
          /\ up \in [Floors -> BOOLEAN]
          /\ destinations \in [Floors -> BOOLEAN]
          
(***************************************************************)
(* To start the car is on the ground floor, there are no up or *)
(* down calls, and no floor is selected                        *)
(***************************************************************)
Init == /\ position    = 0
        /\ down = [f \in Floors |-> FALSE]
        /\ up   = [f \in Floors |-> FALSE]
        /\ destinations = [f \in Floors |-> FALSE]
        

(***********************************************************************)
(* As long as the car is not already on the floor, and there is either *)
(* an up or down call, the car can move directly to that floor         *)
(***********************************************************************)
MoveToFloor(f) == /\ position # f
                  /\ 
                     \/ up[f] = TRUE 
                     \/ down[f] = TRUE
                  /\ position' = f
                  /\ UNCHANGED<<up, down, destinations>>

(***********************************************************************)
(* A user going down calls the elevator, as long as the car is not     *) 
(* already on that floor, and the car has not already been called,     *) 
(* down[f] becomes true                                                *)
(***********************************************************************)
DownCall(f) == /\ f # 0
               /\ down[f] = FALSE
               /\ down' = [down EXCEPT ![f] = TRUE]
               /\ UNCHANGED<<up, position, destinations>>
                 
                 
(**********************************************************************)
(* Up Call is defined similar to DownCall                             *)
(**********************************************************************)     
UpCall(f) ==   /\ f # NumFloors-1
               /\ up[f] = FALSE
               /\ up' = [up EXCEPT ![f] = TRUE]
               /\ UNCHANGED<<down, position, destinations>>

(**********************************************************************)
(* The elevator may pickup a passenger going either direction provided*)
(* the car is on that floor and there is a passenger waiting.  Their  *)
(* destination floor is set to true in destinations                   *)
(**********************************************************************)
PickupGoingUp(f, destination) ==  /\ position = f
                                  /\ up[f] = TRUE
                                  /\ up' = [up EXCEPT ![f] = FALSE]
                                  /\ destinations' = [destinations EXCEPT ![destination] = TRUE]
                                  /\ UNCHANGED<<down, position>>
                              

PickupGoingDown(f, destination) ==  /\ position = f
                                    /\ down[f] = TRUE
                                    /\ down' = [down EXCEPT ![f] = FALSE]
                                    /\ destinations' = [destinations EXCEPT ![destination] = TRUE]
                                    /\ UNCHANGED<<up, position>>

                                 
(*********************************************************************)
(* When the elevator is on a given floor, and that floor is in       *)
(* destinations, destianations for that floor moves to false to      *) 
(* indicate passengers have been dropped of                          *)
(*********************************************************************)                         
Dropoff(f) == /\ position = f
              /\ destinations[f] = TRUE
              /\ destinations' = [destinations EXCEPT ![f] = FALSE]
              /\ UNCHANGED<<position, up, down>>
            

(********************************************************************)
(* Next state transition is:                                        *)
(* The elevator car may move to a floor, be called by a passenger   *)
(* going up or down,  and pickup or drop off passenges              *)
(*                                                                  *)
(********************************************************************)
Next == \/ \E f \in Floors : MoveToFloor(f)
        \/ \E f \in Floors : DownCall(f)
        \/ \E f \in Floors : UpCall(f)
        \/ \E f \in Floors, dest \in Floors : PickupGoingUp(f, dest)
        \/ \E f \in Floors, dest \in Floors : PickupGoingDown(f, dest)
        \/ \E f \in Floors : Dropoff(f)

(*******************************************************************)
(* This temporal formula for liveness states that if an up call    *)
(* occurs on a given floor, the passenger must evetually be picked *)
(* up, which is indicated by the up call being cleared             *)
(*******************************************************************)
Liveness ==  /\ \A f \in Floors : ( up[f] = TRUE ) ~> ( up[f] = FALSE )
             /\ \A f \in Floors : ( destinations[f] = TRUE ) ~> ( destinations[f] = FALSE )



Fairness == /\ \A f \in Floors, dest \in Floors : SF_vars(PickupGoingUp(f, dest))
            /\ \A f \in Floors, dest \in Floors : SF_vars(PickupGoingDown(f, dest))
            /\ \A f \in Floors : SF_vars(Dropoff(f))
            /\ \A f \in Floors : WF_vars(MoveToFloor(f))            
            /\ \A f \in Floors : WF_vars(UpCall(f))            
            /\ \A f \in Floors : WF_vars(DownCall(f))            
            

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ Fairness



=============================================================================
\* Modification History
\* Last modified Mon May 21 21:10:20 PDT 2018 by jennmat
\* Created Thu May 10 21:35:52 PDT 2018 by jennmat
