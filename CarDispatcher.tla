--------------------------- MODULE CarDispatcher ---------------------------

EXTENDS FiniteSets, Integers, Sequences

CONSTANTS
  Passengers,     \* set of all passengers
  Cars    \* set of all cars
  
ASSUME
  IsFiniteSet(Cars)

VARIABLES
  unsat,       \* set of all outstanding requests per passengers
  alloc        \* set of resources allocated to given passenger

TypeOK ==
  /\ unsat \in [Passengers -> SUBSET Cars]
  /\ alloc \in [Passengers -> SUBSET Cars]
  
available == Cars \ (UNION {unsat[p] \cup alloc[p]: p \in Passengers})

Init == 
  /\ unsat = [p \in Passengers |-> {}]
  /\ alloc = [p \in Passengers |-> {}]

Request(p,C) ==
  /\ available # {}
  /\ C \subseteq available
  /\ unsat[p] = {}
  /\ alloc[p] = {}
  /\ unsat' = [unsat EXCEPT ![p] = C]
  /\ UNCHANGED alloc

Pickup(p,C) ==
  /\ C = unsat[p]
  /\ unsat[p] # {}
  /\ alloc[p] = {}
  /\ alloc' = [alloc EXCEPT ![p] = C]
  /\ UNCHANGED unsat  
  
InTransit(p, C) ==
  /\ unsat[p] # {}   
  /\ unsat[p] = alloc[p]
  /\ unsat' = [unsat EXCEPT ![p] = {}]
  /\ UNCHANGED alloc
  
Dropoff(p) ==
  /\ alloc[p] # {}
  /\ alloc' = [alloc EXCEPT ![p] = {}]
  /\ UNCHANGED unsat
  
Next ==
  \/ \E p \in Passengers: Dropoff(p)
  \/ \E p \in Passengers, C \in SUBSET Cars : 
         /\ \/ Request(p,C)
            \/ Pickup(p,C)
            \/ InTransit(p, C)
         /\ Cardinality(C) = 1
  
vars == <<unsat,alloc>>

ResourceMutex ==
  \A p1,p2 \in Passengers : p1 # p2 => alloc[p1] \cap alloc[p2] = {}

PassengerWillBeDroppedOff ==
  \A p \in Passengers : (unsat[p] = {} /\ alloc[p] # {}) ~> alloc[p]={}

PassengerWillBePickedup ==
  \A p \in Passengers, C \in SUBSET Cars: C \in SUBSET unsat[p] ~> C \in SUBSET alloc[p]

InfOftenSatisfied == 
  \A p \in Passengers : []<>(unsat[p] = {})
  
CarDispatcher == 
  /\ Init /\ [][Next]_vars
  /\ \A p \in Passengers: WF_vars(Dropoff(p))
  /\ \A p \in Passengers: SF_vars(\E C \in SUBSET Cars: Pickup(p,C))

THEOREM CarDispatcher => []TypeOK
THEOREM CarDispatcher => []ResourceMutex
THEOREM CarDispatcher => PassengerWillBeDroppedOff
\* THEOREM CarDispatcher2 => ClientsWillReturn
THEOREM CarDispatcher => PassengerWillBePickedup
THEOREM CarDispatcher => InfOftenSatisfied

=============================================================================
\* Modification History
\* Last modified Fri Nov 17 00:27:21 PST 2017 by nanzhu
\* Created Thu Nov 16 12:47:26 PST 2017 by nanzhu
