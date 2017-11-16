`^\Large\bf
TLA+ Model of an improved Zen consensus algorithm ^'
-------------------------------------------------------------------------------------

-------------------------------- MODULE zen -----------------------------------------
\* Imported modules used in this specification
EXTENDS Naturals, FiniteSets, Sequences, TLC

----

\* `^\Large\bf Constants ^'

\* The specification first defines the constants of the model, which amount to values or sets of
\* values that are fixed.

CONSTANTS Values

\* Set of node ids (all master-eligible nodes)
CONSTANTS Nodes

\* The constant "Nil" denotes a place-holder for a non-existing value
CONSTANTS Nil

\* RPC message types
CONSTANTS
  Join, \* only request is modeled
  Publish,
  Apply \* only request is modeled

\* Replication request types
CONSTANTS
  Reconfigure,
  ApplyCSDiff  

----

\* `^\Large\bf Variables ^'

\* The following describes the variable state of the model.

\* Set of in-flight requests and responses sent between nodes.
VARIABLE messages

\* node state
VARIABLE firstUncommittedSlot
VARIABLE currentTerm
VARIABLE currentEra
VARIABLE currentConfiguration
VARIABLE currentClusterState
VARIABLE lastAcceptedTerm
VARIABLE lastAcceptedValue
VARIABLE electionWon
VARIABLE publishPermitted

----

\* Remove request from the set of messages and add response instead
Reply(response, request) == messages' = {response} \cup (messages \ {request})

\* quorums correspond to majority of nodes
IsQuorum(ns, voters) == Cardinality(ns \cap voters) * 2 > Cardinality(voters)

\* set of valid configurations (i.e. all non-empty subsets of Nodes)
ValidConfigs == SUBSET(Nodes) \ {{}}

\* initial model state
Init == /\ messages       = {}
        /\ firstUncommittedSlot = [n \in Nodes |-> 0]
        /\ currentTerm    = [n \in Nodes |-> 0]
        /\ currentEra     = [n \in Nodes |-> 0]
        /\ currentConfiguration \in {[n \in Nodes |-> vc] : vc \in ValidConfigs} \* all agree on initial config
        /\ currentClusterState \in {[n \in Nodes |-> v] : v \in Values} \* all agree on initial value
        /\ lastAcceptedTerm = [n \in Nodes |-> Nil]
        /\ lastAcceptedValue = [n \in Nodes |-> Nil]
        /\ electionWon = [n \in Nodes |-> FALSE]
        /\ publishPermitted = [n \in Nodes |-> FALSE]

\* Send join request from node n to node nm for term t                      
HandleStartJoin(n, nm, t) ==
  /\ t > currentTerm[n]
  /\ (lastAcceptedTerm[n] /= Nil => t > lastAcceptedTerm[n]) 
  /\ LET
       joinRequest == [method  |-> Join,
                       request |-> TRUE,
                       source  |-> n,
                       dest    |-> nm,
                       slot    |-> firstUncommittedSlot[n],
                       term    |-> t,
                       era     |-> currentEra[n],
                       laTerm  |-> lastAcceptedTerm[n]]
     IN
       /\ currentTerm' = [currentTerm EXCEPT ![n] = t]
       /\ publishPermitted' = [publishPermitted EXCEPT ![n] = TRUE]
       /\ electionWon' = [electionWon EXCEPT ![n] = FALSE]
       /\ messages' = messages \cup { joinRequest }
       /\ UNCHANGED <<currentClusterState, currentConfiguration, currentEra, 
                      firstUncommittedSlot, lastAcceptedValue, lastAcceptedTerm>>

\* node n wants to become master and checks if it has received enough joins (= votes) for its term
HandleJoinRequestsToBecomeMaster(n) ==
  LET
    validJoins == { m \in messages : 
      /\ m.method = Join 
      /\ m.request
      /\ m.dest = n
      /\ m.era = currentEra[n] \* voted for the correct era
      /\ m.term = currentTerm[n] \* voted for the correct term
      /\ \/ m.slot < firstUncommittedSlot[n] \* we have a better committed cluster state
         \/ /\ m.slot = firstUncommittedSlot[n] \* we have the same committed cluster state
            /\ (m.laTerm /= Nil => \* but have a better last accepted state
                 (lastAcceptedTerm[n] /= Nil /\ m.laTerm <= lastAcceptedTerm[n]))
    }
    voteGrantingNodes == { m.source : m \in validJoins }
    \* if the voting nodes don't have a value for the next uncommitted slot, we're free to choose any value
    electionValueForced == { m \in validJoins : m.slot = firstUncommittedSlot[n] /\ m.laTerm /= Nil } /= {}
    publishRequests == { [method  |-> Publish,
                          request |-> TRUE,
                          source  |-> n,
                          dest    |-> ns,
                          term    |-> currentTerm[n],
                          era     |-> currentEra[n],
                          slot    |-> firstUncommittedSlot[n],
                          value   |-> lastAcceptedValue[n]] : ns \in Nodes }
  IN
    /\ IsQuorum(voteGrantingNodes, currentConfiguration[n])
    /\ electionWon' = [electionWon EXCEPT ![n] = TRUE]
    /\ messages' = (messages \ validJoins) \cup (IF electionValueForced THEN publishRequests ELSE {})
    /\ publishPermitted' = [publishPermitted EXCEPT ![n] = \lnot electionValueForced]
    /\ UNCHANGED <<currentClusterState, currentConfiguration, currentEra, currentTerm, 
                   firstUncommittedSlot, lastAcceptedValue, lastAcceptedTerm>> 

\* node n (which is master) instructs other nodes to apply change
CommitState(n) ==
  LET
    publishResponses == { m \in messages :
                            /\ m.method = Publish
                            /\ m.request = FALSE
                            /\ m.dest = n
                            /\ m.term = currentTerm[n]
                            /\ m.era = currentEra[n]
                            /\ m.slot = firstUncommittedSlot[n] }
    successResponses == { pr \in publishResponses : pr.success }
    successNodes == { pr.source : pr \in successResponses }
    applyRequests == { [method  |-> Apply,
                        request |-> TRUE,
                        source  |-> n,
                        dest    |-> ns,
                        term    |-> currentTerm[n],
                        era     |-> currentEra[n],
                        slot    |-> firstUncommittedSlot[n]] : ns \in Nodes }
  IN
    /\ IsQuorum(successNodes, currentConfiguration[n])
    /\ messages' = (messages \ publishResponses) \cup applyRequests
    /\ UNCHANGED <<currentClusterState, currentConfiguration, currentEra, currentTerm, electionWon,
                   firstUncommittedSlot, lastAcceptedValue, lastAcceptedTerm, publishPermitted>>


ClientRequest(n, v) ==
  /\ electionWon[n]
  /\ publishPermitted[n]
  /\ LET
       publishRequests == { [request |-> TRUE,
                             method  |-> Publish,
                             source  |-> n,
                             dest    |-> ns,
                             term    |-> currentTerm[n],
                             era     |-> currentEra[n],
                             slot    |-> firstUncommittedSlot[n],
                             value   |-> [type |-> ApplyCSDiff, 
                                          val  |-> (currentClusterState[n] :> v)]
                            ] : ns \in Nodes }
     IN
       /\ publishPermitted' = [publishPermitted EXCEPT ![n] = FALSE]
       /\ messages' = messages \cup publishRequests
       /\ UNCHANGED <<currentClusterState, currentConfiguration, currentEra, currentTerm, electionWon, 
                      firstUncommittedSlot, lastAcceptedValue, lastAcceptedTerm>>


HandlePublishRequest(n, m) ==
  /\ m.method = Publish
  /\ m.request = TRUE
  /\ m.slot = firstUncommittedSlot[n]
  /\ currentTerm[n] <= m.term
  /\ currentEra[n] = m.era
  /\ (lastAcceptedTerm[n] /= Nil => lastAcceptedTerm[n] <= m.term) 
  /\ lastAcceptedTerm' = [lastAcceptedTerm EXCEPT ![n] = m.term]
  /\ lastAcceptedValue' = [lastAcceptedValue EXCEPT ![n] = m.value]
  /\ LET
       response == [method  |-> Publish,
                    request |-> FALSE,
                    source  |-> n,
                    dest    |-> m.source,
                    success |-> TRUE,
                    term    |-> m.term,
                    era     |-> m.era,
                    slot    |-> m.slot]
     IN
       /\ Reply(response, m)
       /\ UNCHANGED <<currentClusterState, currentConfiguration, currentEra, currentTerm, 
                      electionWon, firstUncommittedSlot, publishPermitted>>

ChangeVoters(n, vs) ==
  /\ electionWon[n]
  /\ publishPermitted[n]
  /\ LET
       publishRequests == { [request |-> TRUE,
                             method  |-> Publish,
                             source  |-> n,
                             dest    |-> ns,
                             term    |-> currentTerm[n],
                             era     |-> currentEra[n],
                             slot    |-> firstUncommittedSlot[n],
                             value   |-> [type |-> Reconfigure, val |-> vs]] : ns \in Nodes }
     IN
       /\ publishPermitted' = [publishPermitted EXCEPT ![n] = FALSE]
       /\ messages' = messages \cup publishRequests
       /\ UNCHANGED <<currentClusterState, currentConfiguration, currentEra, currentTerm, 
                      electionWon, firstUncommittedSlot, lastAcceptedValue, lastAcceptedTerm>> 

\* apply committed CS to node
HandleApplyRequest(n, m) ==
  /\ m.method = Apply
  /\ m.request = TRUE
  /\ m.slot = firstUncommittedSlot[n]
  /\ lastAcceptedTerm[n] = m.term
  /\ currentEra[n] = m.era
  /\ firstUncommittedSlot' = [firstUncommittedSlot EXCEPT ![n] = @ + 1]
  /\ lastAcceptedTerm' = [lastAcceptedTerm EXCEPT ![n] = Nil]
  /\ lastAcceptedValue' = [lastAcceptedValue EXCEPT ![n] = Nil]
  /\ publishPermitted' = [publishPermitted EXCEPT ![n] = TRUE]
  /\ IF lastAcceptedValue[n].type = Reconfigure THEN
       /\ currentEra' = [currentEra EXCEPT ![n] = @ + 1]
       /\ currentConfiguration' = [currentConfiguration EXCEPT ![n] = lastAcceptedValue[n].val]
       /\ electionWon' = [electionWon EXCEPT ![n] = FALSE]
       /\ UNCHANGED <<currentClusterState>>
     ELSE
       /\ Assert(lastAcceptedValue[n].type = ApplyCSDiff, "unexpected type")
       /\ Assert(DOMAIN(lastAcceptedValue[n].val) = {currentClusterState[n]}, "diff mismatch")
       /\ currentClusterState' = [currentClusterState EXCEPT ![n] = lastAcceptedValue[n].val[@]] \* apply diff
       /\ UNCHANGED <<currentEra, currentConfiguration, electionWon>> 
  /\ messages' = messages \ {m}
  /\ UNCHANGED <<currentTerm>>

\* drop request or response
DropMessage(m) ==
  /\ messages' = messages \ {m}
  /\ UNCHANGED <<currentClusterState, currentConfiguration, currentEra, currentTerm, electionWon,
                 firstUncommittedSlot, lastAcceptedValue, lastAcceptedTerm, publishPermitted>>

\* crash/restart node n (loses ephemeral state)
RestartNode(n) ==
  /\ electionWon' = [electionWon EXCEPT ![n] = FALSE]
  /\ publishPermitted' = [publishPermitted EXCEPT ![n] = FALSE]
  /\ UNCHANGED <<messages, firstUncommittedSlot, currentTerm, currentEra, currentConfiguration, 
                 currentClusterState, lastAcceptedTerm, lastAcceptedValue>>

\* next-step relation
Next ==
  \/ \E n, nm \in Nodes : HandleStartJoin(n, nm, currentTerm[n] + 1)
  \/ \E n \in Nodes : HandleJoinRequestsToBecomeMaster(n)
  \/ \E n \in Nodes : CommitState(n)
  \/ \E n \in Nodes : \E v \in Values : ClientRequest(n, v)
  \/ \E m \in messages : HandlePublishRequest(m.dest, m)
  \/ \E m \in messages : HandleApplyRequest(m.dest, m)
  \/ \E m \in messages : DropMessage(m)
  \/ \E n \in Nodes : RestartNode(n)
  \/ \E n \in Nodes : \E vs \in ValidConfigs : ChangeVoters(n, vs)

----

\* main invariant:
StateMachineSafety ==
  \A n1, n2 \in Nodes :
    firstUncommittedSlot[n1] = firstUncommittedSlot[n2] => currentClusterState[n1] = currentClusterState[n2]

OneMasterPerTerm ==
  \A n1, n2 \in Nodes :
    n1 /= n2 /\ electionWon[n1] /\ electionWon[n2] => 
      currentTerm[n1] /= currentTerm[n2] \/ currentEra[n1] /= currentEra[n2]

LogMatching ==
  \A n1, n2 \in Nodes :
    /\ currentTerm[n1] = currentTerm[n2]
    /\ currentEra[n1] = currentEra[n2]
    /\ firstUncommittedSlot[n1] = firstUncommittedSlot[n2]
    /\ lastAcceptedTerm[n1] = lastAcceptedTerm[n2]
    => lastAcceptedValue[n1] = lastAcceptedValue[n2]

\* State-exploration limits
StateConstraint ==
  /\ \A n \in Nodes: currentTerm[n] <= 4
  /\ Cardinality(messages) <= 4

====================================================================================================
