--------------------------- MODULE CarDispatcher ---------------------------

EXTENDS FiniteSets, TLC, Integers,Sequences

CONSTANTS
  Passengers,     \* set of all passengers
  Cars,    \* set of all cars
  CarCapacity \* 

ASSUME
  IsFiniteSet(Cars)

VARIABLES
  unsat,       \* set of all outstanding requests per passengers
  alloc        \* set of resources allocated to given passenger
\*  remaining

TypeOK ==
  /\ unsat \in [Passengers -> SUBSET Cars]
  /\ alloc \in [Passengers -> SUBSET Cars]
  
\* TODO: allow partially filled cars
available == Cars \ (UNION {alloc[p] : p \in Passengers})  

Init == 
  /\ unsat = [p \in Passengers |-> {}]
  /\ alloc = [p \in Passengers |-> {}]
\*  /\ remaining = [c \in Cars |-> CarCapacity]

Request(p,C) ==
  /\ Cardinality(C) = 1
  /\ C \subseteq Cars
  /\ unsat[p] = {}
  /\ alloc[p] = {}
  /\ unsat' = [unsat EXCEPT ![p] = C]
  /\ UNCHANGED alloc
\*  /\ UNCHANGED remaining

Pickup(p,C) ==
  /\ Cardinality(C) = 1
  /\ C \subseteq Cars
\*  /\ remaining[CHOOSE c \in C: TRUE] \in Nat
  /\ C \subseteq available \cap unsat[p]
\*  /\ remaining' = [remaining EXCEPT ![CHOOSE c \in C: TRUE] = remaining[CHOOSE c \in C: TRUE] - 1] 
  /\ alloc' = [alloc EXCEPT ![p] = C]
  /\ unsat' = [unsat EXCEPT ![p] = {}]  

Dropoff(p,C) ==
  /\ Cardinality(C) = 1
  /\ C \subseteq Cars 
  /\ C = alloc[p]
\*  /\ remaining' = [remaining EXCEPT ![CHOOSE c \in C: TRUE] = remaining[CHOOSE c \in C: TRUE] + 1]
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
  \A p \in Passengers, c \in SUBSET Cars: c \in unsat[p] ~> c \in alloc[p]

InfOftenSatisfied == 
  \A p \in Passengers : []<>(unsat[p] = {})
  
Symmetry == Permutations(Passengers) \cup Permutations(Cars)

CarDispatcher == 
  /\ Init /\ [][Next]_vars
  /\ \A p \in Passengers: WF_vars(Dropoff(p, alloc[p]))
  /\ \A p \in Passengers: SF_vars(\E C \in SUBSET Cars: Pickup(p,C))

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
\* Last modified Thu Nov 16 16:07:22 PST 2017 by nanzhu
\* Created Thu Nov 16 12:47:26 PST 2017 by nanzhu
