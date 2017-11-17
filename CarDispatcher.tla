--------------------------- MODULE CarDispatcher ---------------------------

EXTENDS FiniteSets, Integers, Sequences, Naturals

CONSTANTS
  Passengers,     \* set of all passengers
  Cars,    \* set of all cars
  Capacity
  
ASSUME
  IsFiniteSet(Cars)

VARIABLES
  unsat,       \* set of all outstanding requests per passengers
  alloc,        \* set of resources allocated to given passenger
  remaining

TypeOK ==
  /\ unsat \in [Passengers -> SUBSET Cars]
  /\ alloc \in [Passengers -> SUBSET Cars]
  /\ \A c \in Cars: remaining[c] \in (Nat \cup {0})

available == {c \in Cars: remaining[c] > 0} 
   
Init == 
  /\ unsat = [p \in Passengers |-> {}]
  /\ alloc = [p \in Passengers |-> {}]
  /\ remaining = [c \in Cars |-> Capacity]

Request(p,C) ==
  /\ available # {}
  /\ C \subseteq available
  /\ unsat[p] = {}
  /\ alloc[p] = {}
  /\ unsat' = [unsat EXCEPT ![p] = C]
  /\ remaining' = [remaining EXCEPT ![CHOOSE c \in C: TRUE] = remaining[CHOOSE c \in C: TRUE] - 1]
  /\ UNCHANGED alloc

Pickup(p,C) ==
  /\ C = unsat[p]
  /\ alloc[p] = {}
  /\ alloc' = [alloc EXCEPT ![p] = C]
  /\ unsat' = [unsat EXCEPT ![p] = {}]
  /\ UNCHANGED remaining  
  
Dropoff(p, C) ==
  /\ alloc[p] # {}
  /\ alloc[p] = C
  /\ alloc' = [alloc EXCEPT ![p] = {}]
  /\ remaining' = [remaining EXCEPT ![CHOOSE c \in C: TRUE] = remaining[CHOOSE c \in C: TRUE] + 1]
  /\ UNCHANGED unsat
  
Next ==
  \/ \E p \in Passengers, C \in SUBSET Cars: Dropoff(p, C)
  \/ \E p \in Passengers, C \in SUBSET Cars :
         /\ Cardinality(C) = 1 
         /\ \/ Request(p,C)
            \/ Pickup(p,C)
  
vars == <<unsat,alloc, remaining>>

ResourceMutex ==
  \A p1,p2 \in Passengers : p1 # p2 => alloc[p1] \cap alloc[p2] = {}

PassengerWillBeDroppedOff ==
  \A p \in Passengers : (unsat[p] = {} /\ alloc[p] # {}) ~> alloc[p]={}

PassengerWillBePickedup ==
  \A p \in Passengers, C \in SUBSET Cars: C \in SUBSET unsat[p] ~> C \in SUBSET alloc[p]

InfOftenSatisfied == 
  /\ \A p \in Passengers : []<>(unsat[p] = {} /\ alloc[p] = {})
  /\ \A c \in Cars : []<>(remaining[c] = Capacity)
  
CarDispatcher == 
  /\ Init /\ [][Next]_vars
  /\ \A p \in Passengers: WF_vars(\E C \in SUBSET alloc[p]: Dropoff(p, C))
  /\ \A p \in Passengers: WF_vars(\E C \in SUBSET unsat[p]: Pickup(p,C))

THEOREM CarDispatcher => []TypeOK
\* THEOREM CarDispatcher => []ResourceMutex
THEOREM CarDispatcher => PassengerWillBeDroppedOff
THEOREM CarDispatcher => PassengerWillBePickedup
THEOREM CarDispatcher => InfOftenSatisfied

=============================================================================
\* Modification History
\* Last modified Fri Nov 17 13:04:17 PST 2017 by nanzhu
\* Created Thu Nov 16 12:47:26 PST 2017 by nanzhu
