--------------------------- MODULE CarDispatcher ---------------------------

EXTENDS FiniteSets, TLC

CONSTANTS
  Passengers,     \* set of all passengers
  Cars    \* set of all cars

ASSUME
  IsFiniteSet(Cars)

VARIABLES
  unsat,       \* set of all outstanding requests per process
  alloc        \* set of resources allocated to given process

TypeOK ==
  /\ unsat \in [Passengers -> SUBSET Cars]
  /\ alloc \in [Passengers -> SUBSET Cars]
  
\* TODO: allow partially filled cars
available == Cars \ (UNION {alloc[p] : p \in Passengers})  

Init == 
  /\ unsat = [p \in Passengers |-> {}]
  /\ alloc = [p \in Passengers |-> {}]

\* TODO: do we need to track C has been allocated? 
Request(p,C) ==
  /\ Cardinality(C) = 1
  /\ unsat[p] = {}
  /\ alloc[p] = {}
  /\ unsat' = [unsat EXCEPT ![p] = C]
  /\ UNCHANGED alloc

Pickup(p,C) ==
  /\ Cardinality(C) = 1
  /\ C \subseteq available \cap unsat[p]
  /\ alloc' = [alloc EXCEPT ![p] = C]
  /\ unsat' = [unsat EXCEPT ![p] = {}]  

Dropoff(p,C) ==
  /\ Cardinality(C) = 1
  /\ C \subseteq Cars
  /\ C = alloc[p]
  /\ alloc' = [alloc EXCEPT ![p] = {}]
  /\ UNCHANGED unsat
  
Next == 
  \E p \in Passengers, C \in SUBSET Cars : 
     (Request(p,C) \/ Pickup(p,C) \/ Dropoff(p,C)) /\ Cardinality(C) = 1
  
vars == <<unsat,alloc>>

\* TODO: temporarily exclusively using a car  
ResourceMutex ==
  \A p1,p2 \in Passengers : p1 # p2 => alloc[p1] \cap alloc[p2] = {}

PassengerWillBeDroppedOff ==
  \A p \in Passengers : unsat[p]={} ~> (alloc[p]={} /\ unsat[p] = {})

PassengerWillBePickedup ==
  \A p \in Passengers, c \in Cars : c \in unsat[p] ~> c \in alloc[p]

InfOftenSatisfied == 
  \A p \in Passengers : []<>(unsat[p] = {})
  
Symmetry == Permutations(Passengers) \cup Permutations(Cars)

CarDispatcher == 
  /\ Init /\ [][Next]_vars
  /\ \A p \in Passengers: WF_vars(Dropoff(p, alloc[p]))
  /\ \A p \in Passengers: SF_vars(\E C \in Cars: Pickup(p,C))

\*PCSpec == PCInit /\ [][PCNext]_<<rmState, aState, msgs>>

(*CarDispatcher2 == 
  /\ Init /\ [][Next]_vars
  /\ \A p \in Passengers: WF_vars(unsat[p] = {} /\ Dropoff(p, alloc[p]))
  /\ \A p \in Passengers: SF_vars(\E C \in Cars: Pickup(p,C))*)  
  
THEOREM CarDispatcher => []TypeOK
THEOREM CarDispatcher => []ResourceMutex
THEOREM CarDispatcher => PassengerWillBeDroppedOff
\* THEOREM SimpleAllocator2 => ClientsWillReturn
THEOREM CarDispatcher => PassengerWillBePickedup
THEOREM CarDispatcher => InfOftenSatisfied

\*THEOREM SimpleAllocator2 => ClientsWillObtain       
\*THEOREM CarDispatcher2 => InfOftenSatisfied       

=============================================================================
\* Modification History
\* Last modified Thu Nov 16 15:09:41 PST 2017 by nanzhu
\* Created Thu Nov 16 12:47:26 PST 2017 by nanzhu
