-------------------------------------------------------------------------------------

-------------------------------- MODULE ZenWithTerms --------------------------------
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
VARIABLE lastAcceptedVersion
VARIABLE lastAcceptedValue
VARIABLE lastAcceptedConfiguration
VARIABLE joinVotes
VARIABLE allowElection
VARIABLE electionWon
VARIABLE publishVersion
VARIABLE lastPublishedConfiguration
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
        /\ lastAcceptedVersion = [n \in Nodes |-> 0]
        /\ lastAcceptedValue \in {[n \in Nodes |-> v] : v \in Values} \* all agree on initial value
        /\ lastAcceptedConfiguration = [n \in Nodes |-> currentConfiguration[n]]
        /\ joinVotes = [n \in Nodes |-> {}]
        /\ allowElection = [n \in Nodes |-> FALSE]
        /\ electionWon = [n \in Nodes |-> FALSE]
        /\ publishVersion = [n \in Nodes |-> 0]
        /\ lastPublishedConfiguration = [n \in Nodes |-> currentConfiguration[n]]
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
                       laVersion |-> lastAcceptedVersion[n]]
     IN
       /\ currentTerm' = [currentTerm EXCEPT ![n] = t]
       /\ publishVersion' = [publishVersion EXCEPT ![n] = 0]
       /\ lastPublishedConfiguration' = [lastPublishedConfiguration EXCEPT ![n] = lastAcceptedConfiguration[n]]
       /\ allowElection' = [allowElection EXCEPT ![n] = TRUE]
       /\ electionWon' = [electionWon EXCEPT ![n] = FALSE]
       /\ joinVotes' = [joinVotes EXCEPT ![n] = {}]
       /\ publishVotes' = [publishVotes EXCEPT ![n] = {}]
       /\ messages' = messages \cup { joinRequest }
       /\ UNCHANGED <<currentConfiguration, lastAcceptedConfiguration, lastAcceptedVersion,
                      lastAcceptedValue, lastAcceptedTerm, descendant>>

\* node n handles a join request and checks if it has received enough joins (= votes)
\* for its term to be elected as master
HandleJoinRequest(n, m) ==
  /\ m.method = Join
  /\ m.term = currentTerm[n]
  /\ allowElection[n]
  /\ \/ m.laTerm < lastAcceptedTerm[n]
     \/ /\ m.laTerm = lastAcceptedTerm[n]
        /\ m.laVersion <= lastAcceptedVersion[n]
  /\ joinVotes' = [joinVotes EXCEPT ![n] = @ \cup { m.source }]
  /\ electionWon' = [electionWon EXCEPT ![n] = ElectionWon(n, joinVotes'[n])]
  /\ IF electionWon[n] = FALSE /\ electionWon'[n]
     THEN
       \* initiating publish version with last accepted version to enable client requests
       /\ publishVersion' = [publishVersion EXCEPT ![n] = lastAcceptedVersion[n]]
     ELSE
       UNCHANGED <<publishVersion>>
  /\ UNCHANGED <<currentConfiguration, currentTerm, publishVotes, messages, descendant,
                 lastAcceptedVersion, lastAcceptedValue, lastAcceptedConfiguration,
                 lastAcceptedTerm, allowElection, lastPublishedConfiguration>>

\* client causes a cluster state change v with configuration vs
ClientRequest(n, v, vs) ==
  /\ electionWon[n]
  /\ publishVersion[n] = lastAcceptedVersion[n] \* means we have the last published value / config (useful for CAS operations, where we need to read the previous value first)
  /\ vs /= lastAcceptedConfiguration[n] => currentConfiguration[n] = lastAcceptedConfiguration[n] \* only allow reconfiguration if there is not already a reconfiguration in progress
  /\ IsQuorum(joinVotes[n], vs) \* only allow reconfiguration if we have a quorum of (join) votes for the new config
  /\ LET
       newPublishVersion == publishVersion[n] + 1
       publishRequests == { [method   |-> PublishRequest,
                             source   |-> n,
                             dest     |-> ns,
                             term     |-> currentTerm[n],
                             version  |-> newPublishVersion,
                             value    |-> v,
                             config   |-> vs,
                             currConf |-> currentConfiguration[n]] : ns \in Nodes }
        newEntry == [prevT |-> lastAcceptedTerm[n],
                     prevV |-> lastAcceptedVersion[n],
                     nextT |-> currentTerm[n],
                     nextV |-> newPublishVersion]
        matchingElems == { e \in descendant : 
                                /\ e.nextT = newEntry.prevT
                                /\ e.nextV = newEntry.prevV }
        newTransitiveElems == { [prevT |-> e.prevT,
                     prevV |-> e.prevV,
                     nextT |-> newEntry.nextT,
                     nextV |-> newEntry.nextV] : e \in matchingElems }
     IN
       /\ descendant' = descendant \cup {newEntry} \cup newTransitiveElems
       /\ publishVersion' = [publishVersion EXCEPT ![n] = newPublishVersion]
       /\ lastPublishedConfiguration' = [lastPublishedConfiguration EXCEPT ![n] = vs]
       /\ publishVotes' = [publishVotes EXCEPT ![n] = {}] \* publishVotes are only counted per publish version
       /\ messages' = messages \cup publishRequests
       /\ UNCHANGED <<allowElection, currentConfiguration, currentTerm, electionWon,
                      lastAcceptedVersion, lastAcceptedValue, lastAcceptedTerm, lastAcceptedConfiguration, joinVotes>>

\* handle publish request m on node n
HandlePublishRequest(n, m) ==
  /\ m.method = PublishRequest
  /\ m.term = currentTerm[n]
  /\ (m.term = lastAcceptedTerm[n]) => (m.version > lastAcceptedVersion[n])
  /\ lastAcceptedTerm' = [lastAcceptedTerm EXCEPT ![n] = m.term]
  /\ lastAcceptedVersion' = [lastAcceptedVersion EXCEPT ![n] = m.version]
  /\ lastAcceptedValue' = [lastAcceptedValue EXCEPT ![n] = m.value]
  /\ lastAcceptedConfiguration' = [lastAcceptedConfiguration EXCEPT ![n] = m.config]
  /\ currentConfiguration' = [currentConfiguration EXCEPT ![n] = m.currConf] 
  /\ LET
       response == [method   |-> PublishResponse,
                    source   |-> n,
                    dest     |-> m.source,
                    term     |-> m.term,
                    version  |-> m.version]
     IN
       /\ messages' = messages \cup {response}
       /\ UNCHANGED <<allowElection, currentTerm, descendant, lastPublishedConfiguration,
                      electionWon, publishVersion, joinVotes, publishVotes>>

\* node n commits a change
HandlePublishResponse(n, m) ==
  /\ m.method = PublishResponse
  /\ m.term = currentTerm[n]
  /\ m.version = publishVersion[n]
  /\ publishVotes' = [publishVotes EXCEPT ![n] = @ \cup {m.source}]
  /\ IF
       /\ IsQuorum(publishVotes'[n], currentConfiguration[n])
       /\ IsQuorum(publishVotes'[n], lastPublishedConfiguration[n])
     THEN
       LET
         commitRequests == { [method   |-> Commit,
                              source   |-> n,
                              dest     |-> ns,
                              term     |-> currentTerm[n],
                              version  |-> publishVersion[n]] : ns \in Nodes }
       IN
         /\ messages' = messages \cup commitRequests
     ELSE
       UNCHANGED <<messages>>
  /\ UNCHANGED <<allowElection, currentConfiguration, currentTerm, electionWon, descendant,
                   lastAcceptedVersion, lastAcceptedValue, lastAcceptedTerm, lastAcceptedConfiguration,
                   publishVersion, lastPublishedConfiguration, joinVotes>>

\* apply committed configuration to node n
HandleCommitRequest(n, m) ==
  /\ m.method = Commit
  /\ m.term = currentTerm[n]
  /\ m.term = lastAcceptedTerm[n]
  /\ m.version = lastAcceptedVersion[n]
  /\ currentConfiguration' = [currentConfiguration EXCEPT ![n] = lastAcceptedConfiguration[n]]
  /\ UNCHANGED <<currentTerm, joinVotes, messages, lastAcceptedTerm, lastAcceptedValue, allowElection, descendant,
                 electionWon, lastAcceptedConfiguration, lastAcceptedVersion, publishVersion, publishVotes,
                 lastPublishedConfiguration>>

\* crash/restart node n (loses ephemeral state)
RestartNode(n) ==
  /\ electionWon' = [electionWon EXCEPT ![n] = FALSE]
  /\ allowElection' = [allowElection EXCEPT ![n] = FALSE]
  /\ joinVotes' = [joinVotes EXCEPT ![n] = {}]
  /\ publishVersion' = [publishVersion EXCEPT ![n] = 0]
  /\ lastPublishedConfiguration' = [lastPublishedConfiguration EXCEPT ![n] = lastAcceptedConfiguration[n]]
  /\ publishVotes' = [publishVotes EXCEPT ![n] = {}]
  /\ UNCHANGED <<messages, lastAcceptedVersion, currentTerm, currentConfiguration, descendant,
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
    /\ IF electionWon[n] THEN publishVersion[n] >= lastAcceptedVersion[n] ELSE publishVersion[n] = 0
    /\ electionWon[n] => allowElection[n]
    /\ publishVotes[n] /= {} => electionWon[n]

OneMasterPerTerm ==
  \A m1, m2 \in messages:
    /\ m1.method = PublishRequest
    /\ m2.method = PublishRequest
    /\ m1.term = m2.term
    => m1.source = m2.source

LogMatching ==
  \A m1, m2 \in messages:
    /\ m1.method = PublishRequest
    /\ m2.method = PublishRequest
    /\ m1.term = m2.term
    /\ m1.version = m2.version
    => m1.value = m2.value

CommittedPublishRequest(mp) ==
  /\ mp.method = PublishRequest
  /\ \E mc \in messages:
       /\ mc.method = Commit
       /\ mp.term = mc.term
       /\ mp.version = mc.version

DescendantRelationIsStrictlyOrdered ==
  /\ \A d \in descendant:
       /\ d.prevT <= d.nextT
       /\ d.prevV < d.nextV
  \* relation is transitive
  /\ \A d1, d2 \in descendant:
       d1.nextT = d2.prevT /\ d1.nextV = d2.prevV 
       => [prevT |-> d1.prevT, prevV |-> d1.prevV, nextT |-> d2.nextT, nextV |-> d2.nextV] \in descendant

NewerOpsBasedOnOlderCommittedOps ==
  \A m1, m2 \in messages :
      /\ CommittedPublishRequest(m1)
      /\ m2.method = PublishRequest
      /\ m2.term >= m1.term
      /\ m2.version > m1.version
      => [prevT |-> m1.term, prevV |-> m1.version, nextT |-> m2.term, nextV |-> m2.version] \in descendant

\* main invariant (follows from NewerOpsBasedOnOlderCommittedOps):
CommittedValuesDescendantsFromCommittedValues ==
  \A m1, m2 \in messages : 
      /\ CommittedPublishRequest(m1)
      /\ CommittedPublishRequest(m2)
      /\ \/ m1.term /= m2.term
         \/ m1.version /= m2.version
    =>
      \/ [prevT |-> m1.term, prevV |-> m1.version, nextT |-> m2.term, nextV |-> m2.version] \in descendant 
      \/ [prevT |-> m2.term, prevV |-> m2.version, nextT |-> m1.term, nextV |-> m1.version] \in descendant

CommittedValuesDescendantsFromInitialValue ==
  \A m \in messages : 
      CommittedPublishRequest(m)
    =>
      [prevT |-> 0, prevV |-> 0, nextT |-> m.term, nextV |-> m.version] \in descendant

\* State-exploration limits
StateConstraint ==
  /\ \A n \in Nodes: IF currentTerm[n] <= 1 THEN publishVersion[n] <= 2 ELSE publishVersion[n] <= 3
  /\ Cardinality(messages) <= 15

====================================================================================================
