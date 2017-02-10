-------------------------------------------- MODULE zen --------------------------------------------
\* Imported modules used in this specification
EXTENDS Naturals, FiniteSets, Sequences, TLC

\* Set of node ids (all master-eligible nodes)
CONSTANTS Nodes

\* Map from Nodes to node id, adding an order on the nodes
CONSTANTS NodeOrder

\* The constant "Nil" denotes a place-holder for a non-existing value
CONSTANTS Nil


CONSTANTS
  Unicast, \* internal:discovery/zen/unicast (this is the pinging)
  Join,    \* internal:discovery/zen/join (only model request, not response)
  Publish, \* internal:discovery/zen/publish/send
  Commit   \* internal:discovery/zen/publish/commit (only model request, response is irrelevant)

(* Not modeled:

  internal:discovery/zen/join/validate (Its just used to check if connection can be established from master to node)
  internal:discovery/zen/leave (covered by NodeFaultDetection rule)
  internal:discovery/zen/fd/master_ping (covered by MasterFaultDetection rule)
  internal:discovery/zen/fd/ping (covered by NodeFaultDetection rule)
  internal:discovery/zen/rejoin (used when master detects that another master is in town to tell it to rejoin - covered by rule to rejoin at any moment?)
*)


CONSTANTS
  Candidate, \* initial state, pinging is done in this state
  Become_Follower, \* pinging established another node should be master, send join request to that node
  Follower, \* node succefully joined a cluster 
  Become_Master, \* pinging established this node should be master, wait for joins
  Master \* node succefully became a master (successfully published cluster state)

----

\* The following describes the variable state of the model.

\* Set of in-flight requests and responses sent between nodes.
VARIABLE messages

\* For simplicity we assume that each client cluster state update request chooses a new unique value
\* to be added to the cluster state.
\* This is just a natural number incremented on each client operation.
VARIABLE nextClientValue

\* The following variables capture state on a per-node basis (maps with domain nodes).

(*
  Possible discovery states:
  - candidate
  - become_follower (used when joining other node)
  - follower (joining successfully completed)
  - become_master (used when waiting for joins from other nodes)
  - master (successfully elected)
*)
VARIABLE discoState

(*
  cluster state: record containing
    subset of nodes that are part of cluster, and a master node field which is either a node id or Nil
    also a field for some data that is currently stored, maybe a sequence of client events (which are just a number increased on every client request)
    and cluster state version field (and make sure version is incremented...)
*)
VARIABLE publishedState \* used by disco module, persisted whenever updated
VARIABLE appliedState \* state visible to the other modules in the cluster

VARIABLE committedStates \* map from publish id to {TRUE, FALSE} to determine if CS has already been successfully published or publishing already failed

VARIABLE nextPublishingId \* map from node id to next publishing id that the node should use for publishing, Allows to distinguish different publishing rounds


(* random comments?
is it important to model waiting for completed join request? Isn't it enough to receive the published CS? 

timeouts are modeled by randomly failing the request early

is it necessary to validate incoming state when in Become_Follower mode by checking if the state comes from the right master?

when publishing fails and in master mode, go back to candidate mode and start pinging again

when in follower mode, store master that is being followed. When receiving cluster state, determine whether it comes from the master we are following. If not, reject it.
How to go back to election mode? Well, we have to wait for response to join request to be failed, then we go

locally count incoming join requests (should be per persistent node id of disco-node, currently it is ephemeral, i.e. the same node can vote twice by just restarting)

*)

\* Return the minimum value from a set, or undefined if the set is empty.
Min(s) == CHOOSE x \in s : \A y \in s : x <= y

\* Return the maximum value from a set, or undefined if the set is empty.
Max(s) == CHOOSE x \in s : \A y \in s : x >= y 

\* Remove request from the set of messages and add response instead
Reply(response, request) == messages' = {response} \cup (messages \ {request})

\* minimum_master_nodes configured to quorum of nodes
MinMasterNodes == (Cardinality(Nodes) \div 2) + 1

InitialDiscoState == [n \in Nodes |-> Candidate]

\* initial cluster state for node n
InitialClusterState(n) == [nodes   |-> {n},
                           master  |-> Nil,
                           version |-> 0,
                           data    |-> << >>]

\* instead of the above, let's initially assume a cluster that is fully started with node 1 as master and all others as followers
StartedInitialDiscoState == [n1 |-> Master] @@ [n \in (Nodes \ {"n1"}) |-> Follower]
StartedInitialClusterState == [nodes   |-> Nodes,
                        master  |-> CHOOSE i \in DOMAIN StartedInitialDiscoState :
                                    StartedInitialDiscoState[i] = Master,
                        version |-> 1,
                        data    |-> << >>]

Init == /\ messages           = {}
        /\ nextClientValue    = 1
        /\ nextPublishingId   = [n \in Nodes |-> 1]
        /\ publishedState     = [n \in Nodes |-> StartedInitialClusterState]
        /\ appliedState       = publishedState
        /\ discoState         = StartedInitialDiscoState
        /\ committedStates    = [n \in Nodes |-> << >>]

\* Send a ping from node n
SendPingRequest(n) ==
  /\ discoState[n] = Candidate \* only send pings when in candidate mode
  /\ LET
       pings == {([method  |-> Unicast,
                   request |-> TRUE,
                   source  |-> n,
                   dest    |-> on]) : on \in (Nodes \ {n})} \* send pings to all the nodes, we can still decide later not to act on some of the responses
     IN
       /\ messages' = messages \cup pings
       /\ UNCHANGED <<nextClientValue, publishedState, appliedState, discoState, nextPublishingId, committedStates>>

\* Node n receives ping request m
HandlePingRequest(n, m) ==
  /\ m.method = Unicast
  /\ m.request = TRUE
  /\ LET
       response == [method  |-> Unicast,
                    request |-> FALSE,
                    source  |-> n,
                    dest    |-> m.source,
                    master  |-> publishedState[n].master,
                    version |-> publishedState[n].version]
     IN
       /\ Reply(response, m)
       /\ UNCHANGED <<nextClientValue, publishedState, appliedState, discoState, nextPublishingId, committedStates>>

\* Helper function to determine based on ping responses which node should become master
FindMaster(pingResponses, self, selfVersion) ==
  LET
    activeMasters == {pr.master : pr \in pingResponses} \ {Nil, self} \* don't count self as active master
    replyingNodes == {pr.source : pr \in pingResponses} \* Elasticsearch does not use persistent node ids here to count replies (it probably should)
    \* add self as master candidate
    masterCandidates == {[node |-> pr.source, version |-> pr.version] : pr \in pingResponses} \cup {[node |-> self, version |-> selfVersion]}
  IN
    IF activeMasters = {}
    THEN
      IF Cardinality(replyingNodes) + 1 < MinMasterNodes \* +1 for current node which does not send a ping request to itself
      THEN
        Nil
      ELSE
        \* ElectMaster(masterCandidates): take nodes with highest cluster state version: If same, chose by node id
        (CHOOSE m1 \in masterCandidates : \A m2 \in masterCandidates :
          m1.version >= m2.version \/ (m1.version = m2.version /\ NodeOrder[m1.node] >= NodeOrder[m2.node])).node
    ELSE
      \* TieBreakActiveMasters(activeMasters): chose node by id
      CHOOSE n \in activeMasters : \A n2 \in activeMasters : NodeOrder[n] >= NodeOrder[n2]

\* when node is in candidate mode, check ping responses to determine if it should become master or follower
HandlePingResponses(n) ==
  /\ discoState[n] = Candidate
  /\ LET
       pingResponses == { ms \in messages : ms.method = Unicast /\ ms.request = FALSE /\ ms.dest = n }
       foundMaster == FindMaster(pingResponses, n, publishedState[n].version)
     IN
       IF foundMaster = Nil
       THEN
         /\ messages' = messages \ pingResponses
         /\ UNCHANGED <<nextClientValue, publishedState, appliedState, discoState, nextPublishingId, committedStates>>
       ELSE
         IF foundMaster = n
         THEN
           /\ messages' = messages \ pingResponses
           /\ discoState' = [discoState EXCEPT ![n] = Become_Master]
           /\ UNCHANGED <<nextClientValue, publishedState, appliedState, nextPublishingId, committedStates>>
         ELSE
           LET joinRequest == [method  |-> Join,
                               request |-> TRUE,
                               source  |-> n,
                               dest    |-> foundMaster]
           IN
             /\ messages' = (messages \ pingResponses) \cup { joinRequest }
             /\ discoState' = [discoState EXCEPT ![n] = Become_Follower]
             /\ UNCHANGED <<nextClientValue, publishedState, appliedState, nextPublishingId, committedStates>>

\* predicate that checks if an ongoing publishing attempt is still going on.
\* if so, we have to wait for that to be either committed or failed before starting a new publishing attempt
\* In Elasticsearch we wait blockingly on the CS update thread in PublishClusterStateAction.
PreviousStateUpdateCompleted(n) ==
  \/ nextPublishingId[n] = 1 \* very first publish attempt
  \/ nextPublishingId[n] - 1 \in DOMAIN committedStates[n] \* previous attempt was either committed or failed


\* when node is in become_master moode, check if it has received enough joins and try to become master by publishing CS
TryBecomeMaster(n) ==
  /\ discoState[n] = Become_Master
  /\ PreviousStateUpdateCompleted(n)
  /\ LET
       joinRequests == { m \in messages : m.method = Join /\ m.request = TRUE /\ m.dest = n }
       joiningNodes == { ns.source : ns \in joinRequests }
       newState == [publishedState[n] EXCEPT !.master = n, !.nodes = @ \cup joiningNodes, !.version = @ + 1]
       publishRequests == { [request |-> TRUE,
                             method  |-> Publish,
                             source  |-> n,
                             dest    |-> ns,
                             id      |-> nextPublishingId[n],
                             state   |-> newState] : ns \in (newState.nodes \ {n}) }
     IN
       /\ Cardinality(joiningNodes) + 1 >= MinMasterNodes \* +1 as we don't send a join request to ourselves
       /\ nextPublishingId' = [nextPublishingId EXCEPT ![n] = @ + 1]
       /\ messages' = (messages \ joinRequests) \cup publishRequests
       /\ UNCHANGED <<nextClientValue, discoState, publishedState, appliedState, committedStates>>

\* when node is a master and join request from another node is received, try to add that node
HandleJoinRequestWhenMaster(n, m) ==
  /\ m.method = Join
  /\ m.request = TRUE
  /\ discoState[n] = Master
  /\ PreviousStateUpdateCompleted(n)
  /\ LET
       joinRequests == { ms \in messages : ms.request = TRUE /\ ms.method = Join /\ ms.dest = n }
       joiningNodes == { ns.source : ns \in joinRequests }
       newState == [publishedState[n] EXCEPT !.nodes = @ \cup joiningNodes, !.version = @ + 1]
       publishRequests == { [request |-> TRUE,
                             method  |-> Publish,
                             source  |-> n,
                             dest    |-> ns,
                             id      |-> nextPublishingId[n],
                             state   |-> newState] : ns \in (newState.nodes \ {n}) }
     IN
       /\ messages' = (messages \ joinRequests) \cup publishRequests
       /\ nextPublishingId' = [nextPublishingId EXCEPT ![n] = @ + 1]
       /\ UNCHANGED <<nextClientValue, discoState, publishedState, appliedState, committedStates>>

DefaultPublishResponse(m) ==
  [method  |-> m.method,
   request |-> FALSE,
   source  |-> m.dest,
   dest    |-> m.source,
   id      |-> m.id,
   success |-> TRUE,
   state   |-> m.state]

\* when node is follower or becoming a follower, handle incoming cluster state
HandlePublishRequest(n, m) ==
  /\ m.request = TRUE
  /\ m.method = Publish
  /\ LET myMaster == publishedState[n].master
         myVersion == publishedState[n].version
         response == DefaultPublishResponse(m)
         failedResponse == [response EXCEPT !.success = FALSE]
     IN
       IF \/ discoState[n] \notin { Become_Follower, Follower }
          \/ myMaster /= Nil /\ m.state.master /= myMaster
          \/ myMaster /= Nil /\ myMaster = m.state.master /\ myVersion > m.state.version
          \/ myMaster = m.state.master /\ myVersion = m.state.version
          \/ myMaster /= Nil /\ myVersion > m.state.version
       THEN
         /\ Reply(failedResponse, m)
         /\ UNCHANGED <<nextClientValue, discoState, publishedState, appliedState, nextPublishingId, committedStates>>
       ELSE
         /\ publishedState' = [publishedState EXCEPT ![n] = m.state]
         /\ discoState' = [discoState EXCEPT ![n] = Follower]
         /\ Reply(response, m)
         /\ UNCHANGED <<nextClientValue, appliedState, nextPublishingId, committedStates>>

\* commit or fail cluster state based on publishing responses
CommitOrFailClusterState(n, m) ==
  /\ m.method = Publish
  /\ m.request = FALSE
  /\ m.id \notin DOMAIN committedStates[n]
  /\ LET
       publishResponses == { ms \in messages : ms.request = FALSE /\ ms.method = Publish /\ ms.dest = n /\ ms.id = m.id }
       successResponses == { pr \in publishResponses : pr.success }
       failedResponses == { pr \in publishResponses : pr.success = FALSE }
       commitRequests == { [method  |-> Commit,
                            request |-> TRUE,
                            source  |-> n,
                            dest    |-> pr.source,
                            state   |-> pr.state] : pr \in publishResponses }
       newState == IF publishedState[n].version >= m.state.version THEN publishedState[n] ELSE m.state
     IN
       \/ \* quorum of nodes accepted state
          /\ discoState[n] \in {Become_Master, Master}
          /\ Cardinality(successResponses) + 1 >= MinMasterNodes \* +1 as we don't send a publish request to ourselves
          /\ committedStates' = [committedStates EXCEPT ![n] = @ @@ (m.id :> TRUE)]
          /\ messages' = (messages \ publishResponses) \cup commitRequests
          /\ discoState' = [discoState EXCEPT ![n] = Master]
          /\ publishedState' = [publishedState EXCEPT ![n] = newState]
          /\ appliedState' = [appliedState EXCEPT ![n] = newState]
          /\ UNCHANGED <<nextClientValue, nextPublishingId>>
       \/ \* quorum of nodes rejected state
          /\ discoState[n] \notin {Become_Master, Master} \/ Cardinality(failedResponses) >= MinMasterNodes
          /\ committedStates' = [committedStates EXCEPT ![n] = @ @@ (m.id :> FALSE)]
          /\ messages' = messages \ publishResponses
          /\ discoState' = [discoState EXCEPT ![n] = Candidate] \* step down as master
          /\ publishedState' = [publishedState EXCEPT ![n].master = Nil]
          /\ appliedState' = [appliedState EXCEPT ![n] = publishedState'[n]]
          /\ UNCHANGED <<nextClientValue, nextPublishingId>>

\* commit or ignore publish response that has already been marked as committed or failed
HandleCommittedPublishResponse(n, m) ==
  /\ m.method = Publish
  /\ m.request = FALSE
  /\ m.id \in DOMAIN committedStates[n]
  /\ IF m.success /\ committedStates[n][m.id] = TRUE /\ discoState[n] \in {Become_Master, Master}
     THEN 
       LET
         commitRequest == [method  |-> Commit,
                           request |-> TRUE,
                           source  |-> n,
                           dest    |-> m.source,
                           state   |-> m.state]
       IN
         /\ Reply(commitRequest, m)
         /\ UNCHANGED <<nextClientValue, nextPublishingId, discoState, publishedState, appliedState, committedStates>>
     ELSE
       \* just ignore
       /\ messages' = messages \ {m}
       /\ UNCHANGED <<nextClientValue, nextPublishingId, discoState, publishedState, appliedState, committedStates>>

\* Follower node receives commit request (i.e. should apply discoState)
HandleCommitRequest(n, m) ==
  /\ m.method = Commit
  /\ m.request = TRUE
  /\ discoState[n] = Follower
  /\ publishedState[n] = m.state \* check that commit request is for the current publishedState
  /\ appliedState' = [appliedState EXCEPT ![n] = m.state] \* apply state
  /\ messages' = messages \ {m}
  /\ UNCHANGED <<nextClientValue, nextPublishingId, publishedState, discoState, committedStates>>

\* publish client cluster state update request
PublishClientRequest(n) ==
  /\ discoState[n] = Master
  /\ PreviousStateUpdateCompleted(n)
  /\ LET
       newState == [publishedState[n] EXCEPT !.data = Append(@, nextClientValue), !.version = @ + 1]
       publishRequests == { [request |-> TRUE,
                             method  |-> Publish,
                             source  |-> n,
                             dest    |-> ns,
                             id      |-> nextPublishingId[n],
                             state   |-> newState] : ns \in (newState.nodes \ {n}) }
     IN
       /\ nextClientValue' = nextClientValue + 1
       /\ nextPublishingId' = [nextPublishingId EXCEPT ![n] = @ + 1]
       /\ messages' = messages \cup publishRequests
       /\ UNCHANGED <<publishedState, appliedState, discoState, committedStates>>

\* drop publish response, replace by failed response
DropPublishResponse(m) ==
  /\ m.method = Publish
  /\ m.request = FALSE
  /\ m.success
  /\ Reply([m EXCEPT !.success = FALSE], m)
  /\ UNCHANGED <<nextClientValue, nextPublishingId, publishedState, appliedState, discoState, committedStates>>

\* drop publish request, replace by failed response
DropPublishRequest(m) ==
  /\ m.method = Publish
  /\ m.request = TRUE
  /\ Reply([DefaultPublishResponse(m) EXCEPT !.success = FALSE], m)
  /\ UNCHANGED <<nextClientValue, nextPublishingId, publishedState, appliedState, discoState, committedStates>>

\* master fault detection on follower node n kicks itself out
MasterFaultDetectionKicksNodeOut(n) ==
  /\ discoState[n] \in {Become_Follower, Follower}
  /\ discoState' = [discoState EXCEPT ![n] = Candidate]
  /\ publishedState' = [publishedState EXCEPT ![n].master = Nil]
  /\ appliedState' = [appliedState EXCEPT ![n].master = Nil]
  /\ UNCHANGED <<nextClientValue, nextPublishingId, messages, committedStates>>

\* node fault detection on master node n kicks node nk out
NodeFaultDetectionKicksNodeOut(n, nk) ==
  /\ discoState[n] = Master
  /\ PreviousStateUpdateCompleted(n)
  /\ nk \in publishedState[n].nodes \* node to be kicked out is actually one of the known nodes
  /\ LET
       newState == [publishedState[n] EXCEPT !.nodes = @ \ {nk}, !.version = @ + 1]
       publishRequests == { [request |-> TRUE,
                             method  |-> Publish,
                             source  |-> n,
                             dest    |-> ns,
                             id      |-> nextPublishingId[n],
                             state   |-> newState] : ns \in (newState.nodes \ {n}) }
     IN
       IF Cardinality(newState.nodes) < MinMasterNodes
       THEN
         \* step down as master
         /\ discoState' = [discoState EXCEPT ![n] = Candidate]
         /\ publishedState' = [publishedState EXCEPT ![n].master = Nil]
         /\ appliedState' = [appliedState EXCEPT ![n].master = Nil]
         /\ UNCHANGED <<nextClientValue, nextPublishingId, committedStates, messages>>
       ELSE
         \* publish
         /\ nextPublishingId' = [nextPublishingId EXCEPT ![n] = @ + 1]
         /\ messages' = messages \cup publishRequests
         /\ UNCHANGED <<nextClientValue, publishedState, appliedState, discoState, committedStates>>

\* restart node n
\* assume at the moment that all state is dropped
RestartNode(n) ==
  /\ discoState' = [discoState EXCEPT ![n] = Candidate]
  /\ publishedState' = [publishedState EXCEPT ![n] = InitialClusterState(n)]
  /\ appliedState' = [appliedState EXCEPT ![n] = InitialClusterState(n)]
  /\ committedStates' = [committedStates EXCEPT ![n] = << >>]
  /\ nextPublishingId' = [nextPublishingId EXCEPT ![n] = 1]
  /\ UNCHANGED <<nextClientValue, messages>>

\* next-step relation
Next ==
  \/ \E n \in Nodes : SendPingRequest(n)
  \/ \E n \in Nodes : HandlePingResponses(n)
  \/ \E m \in messages : HandlePingRequest(m.dest, m)
  \/ \E n \in Nodes : TryBecomeMaster(n)
  \/ \E m \in messages : HandleJoinRequestWhenMaster(m.dest, m)
  \/ \E m \in messages : HandlePublishRequest(m.dest, m)
  \/ \E m \in messages : CommitOrFailClusterState(m.dest, m)
  \/ \E m \in messages : HandleCommittedPublishResponse(m.dest, m)
  \/ \E m \in messages : HandleCommitRequest(m.dest, m)
  \/ \E m \in messages : DropPublishRequest(m)
  \/ \E m \in messages : DropPublishResponse(m)
  \/ \E n \in Nodes : PublishClientRequest(n)
  \/ \E n \in Nodes : MasterFaultDetectionKicksNodeOut(n)
  \/ \E n1, n2 \in Nodes : NodeFaultDetectionKicksNodeOut(n1, n2)
  \* \/ \E n \in Nodes : RestartNode(n)

----

\* ensure consistency between discoState and publishedState
Wellformed ==
  /\ \A n \in Nodes : discoState[n] = Master <=> publishedState[n].master = n 
  /\ \A n1 \in Nodes : discoState[n1] = Follower <=> (\E n2 \in Nodes : n2 /= n1 /\ publishedState[n1].master = n2)
  /\ \A n \in Nodes : discoState[n] \in {Candidate, Become_Follower, Become_Master} <=> publishedState[n].master = Nil 


\* returns true if seq1 is a prefix of seq2
PrefixOf(seq1, seq2) ==
  LET
    len1 == Len(seq1)
    len2 == Len(seq2)
  IN
    IF len1 <= len2
    THEN
      seq1 = SubSeq(seq2, 1, len1)
    ELSE
      FALSE

\* main invariant:
\* if node n1 has an applied cluster state with version v1 and node n2 has an applied cluster state with version v2:
\*   if v1 <= v2: state1.data must be a prefix of state2.data
\* in particular, when both have the same version, the content must be the same
PreservePrefixOrder ==
  \A n1, n2 \in Nodes :
    LET
      state1 == appliedState[n1]
      state2 == appliedState[n2]
    IN
      state1.version <= state2.version => PrefixOf(state1.data, state2.data)




====================================================================================================
