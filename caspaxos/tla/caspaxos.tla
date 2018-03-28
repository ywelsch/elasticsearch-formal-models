-------------------------------------------------------------------------------------

-------------------------------- MODULE caspaxos ------------------------------------
\* Imported modules used in this specification
EXTENDS Naturals, FiniteSets, Sequences, TLC

----

CONSTANTS Values

\* Set of node ids (all master-eligible nodes)
CONSTANTS Nodes

\* RPC message types
CONSTANTS
  Join,
  PublishRequest,
  PublishResponse,
  Commit

----

\* Set of requests and responses sent between nodes.
VARIABLE messages
\* Transitive closure of value updates as done by leaders 
VARIABLE descendant

\* node state (map from node id to state)
VARIABLE currentTerm
VARIABLE currentConfiguration \* committed config
VARIABLE lastAcceptedTerm
VARIABLE lastAcceptedInstance
VARIABLE lastAcceptedValue
VARIABLE lastAcceptedConfiguration
VARIABLE joinVotes
VARIABLE allowElection
VARIABLE electionWon
VARIABLE publishInstance
VARIABLE publishVotes

----

Terms == Nat

\* set of valid configurations (i.e. the set of all non-empty subsets of Nodes)
ValidConfigs == SUBSET(Nodes) \ {{}}

\* quorums correspond to majority of votes in a config
IsQuorum(votes, config) == Cardinality(votes \cap config) * 2 > Cardinality(config)

ElectionWon(n, votes) ==
  /\ IsQuorum(votes, currentConfiguration[n])
  /\ IsQuorum(votes, lastAcceptedConfiguration[n])

\* initial model state
Init == /\ messages = {}
        /\ descendant = {}
        /\ currentTerm = [n \in Nodes |-> 0]
        /\ currentConfiguration \in {[n \in Nodes |-> vc] : vc \in ValidConfigs} \* all agree on initial config
        /\ lastAcceptedTerm = [n \in Nodes |-> 0]
        /\ lastAcceptedInstance = [n \in Nodes |-> 0]
        /\ lastAcceptedValue \in {[n \in Nodes |-> v] : v \in Values} \* all agree on initial value
        /\ lastAcceptedConfiguration = [n \in Nodes |-> currentConfiguration[n]]
        /\ joinVotes = [n \in Nodes |-> {}]
        /\ allowElection = [n \in Nodes |-> FALSE]
        /\ electionWon = [n \in Nodes |-> FALSE]
        /\ publishInstance = [n \in Nodes |-> 0]
        /\ publishVotes = [n \in Nodes |-> {}]

\* Send join request from node n to node nm for term t
HandleStartJoin(n, nm, t) ==
  /\ t > currentTerm[n]
  /\ LET
       joinRequest == [method     |-> Join,
                       source     |-> n,
                       dest       |-> nm,
                       term       |-> t,
                       laTerm     |-> lastAcceptedTerm[n],
                       laInstance |-> lastAcceptedInstance[n]]
     IN
       /\ currentTerm' = [currentTerm EXCEPT ![n] = t]
       /\ publishInstance' = [publishInstance EXCEPT ![n] = 0]
       /\ allowElection' = [allowElection EXCEPT ![n] = TRUE]
       /\ electionWon' = [electionWon EXCEPT ![n] = FALSE]
       /\ joinVotes' = [joinVotes EXCEPT ![n] = {}]
       /\ publishVotes' = [publishVotes EXCEPT ![n] = {}]
       /\ messages' = messages \cup { joinRequest }
       /\ UNCHANGED <<currentConfiguration, lastAcceptedConfiguration, lastAcceptedInstance,
                      lastAcceptedValue, lastAcceptedTerm, descendant>>

\* node n handles a join request and checks if it has received enough joins (= votes)
\* for its term to be elected as master
HandleJoinRequest(n, m) ==
  /\ m.method = Join
  /\ m.term = currentTerm[n]
  /\ allowElection[n]
  /\ \/ m.laTerm < lastAcceptedTerm[n]
     \/ /\ m.laTerm = lastAcceptedTerm[n]
        /\ m.laInstance <= lastAcceptedInstance[n]
  /\ joinVotes' = [joinVotes EXCEPT ![n] = @ \cup { m.source }]
  /\ electionWon' = [electionWon EXCEPT ![n] = ElectionWon(n, joinVotes'[n])]
  /\ IF electionWon[n] = FALSE /\ electionWon'[n]
     THEN
       /\ Assert(publishInstance[n] = 0, "unexpected publish instance")
       /\ Assert(publishVotes[n] = {}, "unexpected publish votes")
       \* moving publish instance up to last accepted instance to enable client requests, which is safe
       /\ publishInstance' = [publishInstance EXCEPT ![n] = lastAcceptedInstance[n]]
     ELSE
       UNCHANGED <<publishInstance>>
  /\ UNCHANGED <<currentConfiguration, currentTerm, publishVotes, messages, descendant,
                 lastAcceptedInstance, lastAcceptedValue, lastAcceptedConfiguration, lastAcceptedTerm, allowElection>>

\* client causes a cluster state change v with configuration vs
ClientRequest(n, v, vs) ==
  /\ electionWon[n]
  /\ publishInstance[n] = lastAcceptedInstance[n] \* means we have the last published value / config (useful for CAS operations, where we need to read the previous value first)
  /\ vs /= lastAcceptedConfiguration[n] => currentConfiguration[n] = lastAcceptedConfiguration[n] \* only allow reconfiguration if there is not already a reconfiguration in progress
  /\ IsQuorum(joinVotes[n], vs) \* only allow reconfiguration if we have a quorum of (join) votes for the new config
  /\ LET
       newPublishInstance == publishInstance[n] + 1
       publishRequests == { [method   |-> PublishRequest,
                             source   |-> n,
                             dest     |-> ns,
                             term     |-> currentTerm[n],
                             instance |-> newPublishInstance,
                             value    |-> v,
                             config   |-> vs,
                             currConf |-> currentConfiguration[n]] : ns \in Nodes }
        newEntry == [prevT |-> lastAcceptedTerm[n],
                     prevI |-> lastAcceptedInstance[n],
                     nextT |-> currentTerm[n],
                     nextI |-> newPublishInstance]
        matchingElems == { e \in descendant : 
                                /\ e.nextT = newEntry.prevT
                                /\ e.nextI = newEntry.prevI }
        newTransitiveElems == { [prevT |-> e.prevT,
                     prevI |-> e.prevI,
                     nextT |-> newEntry.nextT,
                     nextI |-> newEntry.nextI] : e \in matchingElems }
     IN
       /\ descendant' = descendant \cup {newEntry} \cup newTransitiveElems
       /\ publishInstance' = [publishInstance EXCEPT ![n] = newPublishInstance]
       /\ publishVotes' = [publishVotes EXCEPT ![n] = {}] \* publishVotes are only counted per publish instance
       /\ messages' = messages \cup publishRequests
       /\ UNCHANGED <<allowElection, currentConfiguration, currentTerm, electionWon,
                      lastAcceptedInstance, lastAcceptedValue, lastAcceptedTerm, lastAcceptedConfiguration, joinVotes>>

\* handle publish request m on node n
HandlePublishRequest(n, m) ==
  /\ m.method = PublishRequest
  /\ m.term = currentTerm[n]
  /\ (m.term = lastAcceptedTerm[n]) => (m.instance > lastAcceptedInstance[n])
  /\ lastAcceptedTerm' = [lastAcceptedTerm EXCEPT ![n] = m.term]
  /\ lastAcceptedInstance' = [lastAcceptedInstance EXCEPT ![n] = m.instance]
  /\ lastAcceptedValue' = [lastAcceptedValue EXCEPT ![n] = m.value]
  /\ lastAcceptedConfiguration' = [lastAcceptedConfiguration EXCEPT ![n] = m.config]
  /\ currentConfiguration' = [currentConfiguration EXCEPT ![n] = m.currConf] 
  /\ LET
       response == [method   |-> PublishResponse,
                    source   |-> n,
                    dest     |-> m.source,
                    term     |-> m.term,
                    instance |-> m.instance]
     IN
       /\ messages' = messages \cup {response}
       /\ UNCHANGED <<allowElection, currentTerm, descendant,
                      electionWon, publishInstance, joinVotes, publishVotes>>

\* node n commits a change
HandlePublishResponse(n, m) ==
  /\ m.method = PublishResponse
  /\ m.term = currentTerm[n]
  /\ m.instance = publishInstance[n]
  /\ publishVotes' = [publishVotes EXCEPT ![n] = @ \cup {m.source}]
  /\ IF IsQuorum(publishVotes'[n], currentConfiguration[n])
     THEN
       LET
         commitRequests == { [method   |-> Commit,
                              source   |-> n,
                              dest     |-> ns,
                              term     |-> currentTerm[n],
                              instance |-> publishInstance[n]] : ns \in Nodes }
       IN
         /\ messages' = messages \cup commitRequests
     ELSE
       UNCHANGED <<messages>>
  /\ UNCHANGED <<allowElection, currentConfiguration, currentTerm, electionWon, descendant,
                   lastAcceptedInstance, lastAcceptedValue, lastAcceptedTerm, lastAcceptedConfiguration,
                   publishInstance, joinVotes>>

\* apply committed configuration to node n
HandleCommitRequest(n, m) ==
  /\ m.method = Commit
  /\ m.term = currentTerm[n]
  /\ m.term = lastAcceptedTerm[n]
  /\ m.instance = lastAcceptedInstance[n]
  /\ currentConfiguration' = [currentConfiguration EXCEPT ![n] = lastAcceptedConfiguration[n]]
  /\ UNCHANGED <<currentTerm, joinVotes, messages, lastAcceptedTerm, lastAcceptedValue, allowElection, descendant,
                 electionWon, lastAcceptedConfiguration, lastAcceptedInstance, publishInstance, publishVotes>>

\* crash/restart node n (loses ephemeral state)
RestartNode(n) ==
  /\ electionWon' = [electionWon EXCEPT ![n] = FALSE]
  /\ allowElection' = [allowElection EXCEPT ![n] = FALSE]
  /\ joinVotes' = [joinVotes EXCEPT ![n] = {}]
  /\ publishInstance' = [publishInstance EXCEPT ![n] = 0]
  /\ publishVotes' = [publishVotes EXCEPT ![n] = {}]
  /\ UNCHANGED <<messages, lastAcceptedInstance, currentTerm, currentConfiguration, descendant,
                 lastAcceptedTerm, lastAcceptedValue, lastAcceptedConfiguration>>

\* next-step relation
Next ==
  \/ \E n, nm \in Nodes : \E t \in Terms : HandleStartJoin(n, nm, t)
  \/ \E m \in messages : HandleJoinRequest(m.dest, m)
  \/ \E n \in Nodes : \E v \in Values : \E vs \in ValidConfigs : ClientRequest(n, v, vs)
  \/ \E m \in messages : HandlePublishRequest(m.dest, m)
  \/ \E m \in messages : HandlePublishResponse(m.dest, m)
  \/ \E m \in messages : HandleCommitRequest(m.dest, m)
  \/ \E n \in Nodes : RestartNode(n)

----

\* Invariants

SingleNodeInvariant ==
  \A n \in Nodes :
    /\ lastAcceptedTerm[n] <= currentTerm[n]
    /\ electionWon[n] = ElectionWon(n, joinVotes[n]) \* cached value is consistent

OneMasterPerTerm ==
  \A n1, n2 \in Nodes :
    /\ electionWon[n1]
    /\ electionWon[n2]
    /\ currentTerm[n1] = currentTerm[n2]
    => n1 = n2

OneMasterPerTermMessages ==
  \A m1, m2 \in messages:
    /\ m1.method = PublishRequest
    /\ m2.method = PublishRequest
    /\ m1.term = m2.term
    => m1.source = m2.source

LogMatching ==
  \A n1, n2 \in Nodes :
    /\ lastAcceptedTerm[n1] = lastAcceptedTerm[n2]
    /\ lastAcceptedInstance[n1] = lastAcceptedInstance[n2]
    => lastAcceptedValue[n1] = lastAcceptedValue[n2]

LogMatchingMessages ==
  \A m1, m2 \in messages:
    /\ m1.method = PublishRequest
    /\ m2.method = PublishRequest
    /\ m1.term = m2.term
    /\ m1.instance = m2.instance
    => m1.value = m2.value

CommittedPublishRequest(mp) ==
  /\ mp.method = PublishRequest
  /\ \E mc \in messages:
       /\ mc.method = Commit
       /\ mp.term = mc.term
       /\ mp.instance = mc.instance

DescendantRelationIsStrictlyOrdered ==
  /\ \A d \in descendant:
       \/ d.prevT < d.nextT
       \/ d.prevT = d.nextT /\ d.prevI < d.nextI
  \* relation is transitive
  /\ \A d1, d2 \in descendant:
       d1.nextT = d2.prevT /\ d1.nextI = d2.prevI 
       => [prevT |-> d1.prevT, prevI |-> d1.prevI, nextT |-> d2.nextT, nextI |-> d2.nextI] \in descendant
       
\* main invariant:
CommittedValuesDescendantsFromCommittedValues ==
  \A m1, m2 \in messages : 
      /\ CommittedPublishRequest(m1)
      /\ CommittedPublishRequest(m2)
      /\ \/ m1.term /= m2.term
         \/ m1.instance /= m2.instance
    =>
      \/ [prevT |-> m1.term, prevI |-> m1.instance, nextT |-> m2.term, nextI |-> m2.instance] \in descendant 
      \/ [prevT |-> m2.term, prevI |-> m2.instance, nextT |-> m1.term, nextI |-> m1.instance] \in descendant

CommittedValuesDescendantsFromInitialValue ==
  \A m \in messages : 
      CommittedPublishRequest(m)
    =>
      [prevT |-> 0, prevI |-> 0, nextT |-> m.term, nextI |-> m.instance] \in descendant

\* this does not hold, but this is also not what we would like to check
CommittedValueDirectlyBasedOnCommittedValue ==
  \A m1 \in messages : CommittedPublishRequest(m1) =>
    \/ m1.prevInstance = 0 /\ m1.prevTerm = 0
    \/ \E m2 \in messages :
         /\ CommittedPublishRequest(m2)
         /\ m2.method = PublishRequest
         /\ m2.instance = m1.prevInstance
         /\ m2.term = m1.prevTerm  


\* State-exploration limits
StateConstraint ==
  /\ \A n \in Nodes: publishInstance[n] <= 2
  /\ Cardinality(messages) <= 15

====================================================================================================
