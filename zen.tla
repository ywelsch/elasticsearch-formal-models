-------------------------------------------- MODULE zen --------------------------------------------
\* Imported modules used in this specification
EXTENDS Naturals, FiniteSets, Sequences, TLC

\* Set of node ids (all master-eligible nodes)
CONSTANTS Nodes

\* The constant "Nil" denotes a place-holder for a non-existing value
CONSTANTS Nil

CONSTANTS
  Unicast,
  Join, \* only models request
  AppendEntries,
  Apply \* only models request

CONSTANTS
  Pinging, \* initial state, pinging is done in this state
  Become_Follower, \* pinging established another node should be master, send join request to that node
  Follower, \* node succefully joined a cluster
  Become_Master, \* pinging established this node should be master, wait for joins
  Master \* node successfully became a master (received enough joins and starts publishing CS)

----

\* The following describes the variable state of the model.

\* Set of in-flight requests and responses sent between nodes.
VARIABLE messages

\* For simplicity we assume that each cluster state update chooses a new unique value to be added
\* to the cluster state. This allows us to check that nodes have a consistent view on CS updates.
VARIABLE nextClientValue

\* The following variables capture state on a per-node basis (maps with domain nodes).

(*
  Possible discovery states:
  - pinging
  - become_follower
  - follower
  - become_master
  - master
*)
VARIABLE discoState

(*
  cluster state: record containing
    subset of nodes that are part of cluster, and a master node field which is either a node id or Nil
    also a field for some data that is currently stored, maybe a sequence of client events (which are just a number increased on every client request)
    and cluster state version field (and make sure version is incremented...)
    as well as the term with which this CS was published
*)
VARIABLE publishedState \* used by disco module, persisted whenever updated
VARIABLE term \* used by disco module, persisted
VARIABLE appliedState \* state visible to the other modules on the node

----

\* Return the maximum value from a set, or undefined if the set is empty.
Max(s) == CHOOSE x \in s : \A y \in s : x >= y 

\* Remove request from the set of messages and add response instead
Reply(response, request) == messages' = {response} \cup (messages \ {request})

\* minimum_master_nodes configured to quorum of nodes
MinMasterNodes == (Cardinality(Nodes) \div 2) + 1

InitialDiscoState == [n \in Nodes |-> Pinging]

\* initial cluster state for node n
InitialClusterState(n) == [nodes   |-> {n},
                           master  |-> Nil,
                           version |-> 0,
                           term    |-> 0,
                           data    |-> << >>]

Init == /\ messages           = {}
        /\ nextClientValue    = 1
        /\ publishedState     = [n \in Nodes |-> InitialClusterState(n)]
        /\ appliedState       = publishedState
        /\ discoState         = InitialDiscoState
        /\ term               = [n \in Nodes |-> 0]

SendPingRequest(n) ==
  /\ discoState[n] = Pinging \* only send pings when in Pinging mode
  /\ LET
       \* send pings to all the nodes (except self), we can still decide later not to act on
       \* some of the ping requests/responses
       pings == {([method  |-> Unicast,
                   request |-> TRUE,
                   source  |-> n,
                   dest    |-> on,
                   term    |-> term[n]]) : on \in (Nodes \ {n})} \* add term so that we can disrupt a master/follower with a lower term
     IN
       /\ messages' = messages \cup pings
       /\ UNCHANGED <<nextClientValue, publishedState, appliedState, term, discoState>>

HandlePingRequest(n, m) ==
  /\ m.method = Unicast
  /\ m.request = TRUE
  /\ IF m.term > term[n]
     THEN
       /\ term' = [term EXCEPT ![n] = m.term]
       /\ discoState' = [discoState EXCEPT ![n] = Pinging] \* revert to Pinging state (maybe we could just do this here if we are Master or Follower, but not when Become_Master or Become_Follower)
     ELSE
       UNCHANGED <<term, discoState>>
  /\ LET
       \* use primed variables of discoState and term as they might have been modified by the conjunction above
       response == [method  |-> Unicast,
                    request |-> FALSE,
                    source  |-> n,
                    dest    |-> m.source,
                    master  |-> IF discoState'[n] \in {Master, Follower} THEN publishedState[n].master ELSE Nil,
                    version |-> publishedState[n].version,
                    csTerm  |-> publishedState[n].term,
                    term    |-> term'[n],
                    discoSt |-> discoState'[n]]
     IN
       Reply(response, m)
  /\ UNCHANGED <<nextClientValue, publishedState, appliedState>>

\* when node is in pinging mode, check ping responses to determine if it should become master or follower
HandlePingResponses(n) ==
  /\ discoState[n] = Pinging
  /\ LET
       pingResponses == { ms \in messages : ms.method = Unicast /\ ms.request = FALSE /\ ms.dest = n }
       activeMastersWithAcceptableTerm == { pr \in pingResponses : pr.master \notin {Nil, n} /\ pr.term >= term[n] }
       masterCandidates == pingResponses \cup
                           {[source |-> n,
                             version |-> publishedState[n].version,
                             csTerm |-> publishedState[n].term,
                             term |-> term[n],
                             discoSt |-> discoState[n]]} \* add ping response for self
     IN
       IF Cardinality(activeMastersWithAcceptableTerm) > 0
       THEN
         \E masterToJoin \in activeMastersWithAcceptableTerm:
           LET
             \* send join request to master, but stay in Pinging mode (as current term is not speculative and no voting is happening)
             joinRequest == [method  |-> Join,
                             request |-> TRUE,
                             source  |-> n,
                             dest    |-> masterToJoin.master,
                             term    |-> 0] \* this join request only works if the node is already master and does not constitute a vote
           IN
             /\ messages' = (messages \ pingResponses) \cup { joinRequest }
             /\ UNCHANGED <<nextClientValue, publishedState, appliedState, term, discoState>> \* no voting necessary to join an existing master
       ELSE
         IF Cardinality({pr.source : pr \in masterCandidates}) < MinMasterNodes \* masterCandidates contains self
         THEN
           UNCHANGED <<nextClientValue, publishedState, appliedState, term, discoState, messages>> \* noop
         ELSE
           \E bestCSCandidate \in masterCandidates :
             \A otherCandidate \in masterCandidates : 
               /\ \/ bestCSCandidate.csTerm > bestCSCandidate.csTerm 
                  \/ /\ bestCSCandidate.csTerm = otherCandidate.csTerm
                     /\ bestCSCandidate.version >= otherCandidate.version
               /\ LET
                    \* choose the node with the best cluster state
                    bestCSNode == bestCSCandidate.source
                    \* choose highest term seen + 1. If node is becoming master or follower, it already has a speculative term
                    nextTerm == Max({ IF pr.discoSt \in {Become_Master, Become_Follower} THEN pr.term ELSE pr.term + 1 : pr \in masterCandidates })
                    joinRequest == [method  |-> Join,
                                    request |-> TRUE,
                                    source  |-> n,
                                    dest    |-> bestCSNode,
                                    term    |-> nextTerm]
                  IN
                    /\ term' = [term EXCEPT ![n] = nextTerm]
                    /\ discoState' = [discoState EXCEPT ![n] = IF bestCSNode = n THEN Become_Master ELSE Become_Follower]
                    /\ messages' = (messages \ pingResponses) \cup (IF bestCSNode = n THEN {} ELSE { joinRequest })
                    /\ UNCHANGED <<nextClientValue, publishedState, appliedState>>

\* node n wants to become master and checks if it has received enough joins (= votes) for its prospective term
HandleJoinRequestsToBecomeMaster(n) ==
  /\ discoState[n] = Become_Master
  /\ LET
       sameTermJoins == { m \in messages : m.method = Join /\ m.request /\ m.dest = n /\ m.term = term[n] }
       voteGrantingNodes == { m.source : m \in sameTermJoins }
       newState == [publishedState[n] EXCEPT !.master = n, !.nodes = @ \cup voteGrantingNodes, !.term = term[n], !.version = @ + 1, !.data = Append(@, nextClientValue)]
       publishRequests == { [method  |-> AppendEntries,
                             request |-> TRUE,
                             source  |-> n,
                             dest    |-> ns,
                             term    |-> term[n],
                             state   |-> newState] : ns \in (newState.nodes \ {n}) }
     IN
       /\ Cardinality(voteGrantingNodes) + 1 >= MinMasterNodes \* +1 as we don't send a join request to ourselves
       /\ discoState' = [discoState EXCEPT ![n] = Master]
       /\ publishedState' = [publishedState EXCEPT ![n] = newState]
       /\ nextClientValue' = nextClientValue + 1
       /\ messages' = (messages \ sameTermJoins) \cup publishRequests
       /\ UNCHANGED <<appliedState, term>>

\* node n is master and lets another node join
HandleJoinRequestWhenMaster(n) ==
  /\ discoState[n] = Master
  /\ publishedState[n] = appliedState[n] \* previous round was committed
  /\ LET
       joinRequests == { m \in messages : m.method = Join /\ m.request /\ m.dest = n }
       newState == [publishedState[n] EXCEPT !.master = n, !.nodes = @ \cup { m.source : m \in joinRequests }, !.term = term[n], !.version = @ + 1, !.data = Append(@, nextClientValue)]
       publishRequests == { [method  |-> AppendEntries,
                             request |-> TRUE,
                             source  |-> n,
                             dest    |-> ns,
                             term    |-> term[n],
                             state   |-> newState] : ns \in (newState.nodes \ {n}) }
     IN
       /\ publishedState' = [publishedState EXCEPT ![n] = newState]
       /\ nextClientValue' = nextClientValue + 1
       /\ messages' = (messages \ joinRequests) \cup publishRequests
       /\ UNCHANGED <<appliedState, discoState, term>>

\* node n (which is master) instructs other nodes to apply CS
CommitState(n) ==
  LET
    publishResponses == { m \in messages :
                            /\ m.method = AppendEntries
                            /\ m.request = FALSE
                            /\ m.dest = n
                            /\ m.term = term[n] \* can only commit stuff from my term
                            /\ m.version = publishedState[n].version }
    successResponses == { pr \in publishResponses : pr.success }
    applyRequests == { [method  |-> Apply,
                        request |-> TRUE,
                        source  |-> n,
                        dest    |-> ns,
                        state   |-> publishedState[n]] : ns \in (publishedState[n].nodes \ {n}) }
  IN
    /\ Cardinality(successResponses) + 1 >= MinMasterNodes \* +1 as we don't send publish request to ourselves
    /\ messages' = (messages \ publishResponses) \cup applyRequests
    /\ appliedState' = [appliedState EXCEPT ![n] = publishedState[n]]
    /\ UNCHANGED <<nextClientValue, discoState, publishedState, term>>


ClientRequest(n) ==
  /\ discoState[n] = Master
  /\ publishedState[n] = appliedState[n] \* previous round was committed
  /\ LET
       newState == [publishedState[n] EXCEPT !.data = Append(@, nextClientValue), !.version = @ + 1]
       publishRequests == { [request |-> TRUE,
                             method  |-> AppendEntries,
                             source  |-> n,
                             dest    |-> ns,
                             term    |-> term[n],
                             state   |-> newState] : ns \in (newState.nodes \ {n}) }
     IN
       /\ nextClientValue' = nextClientValue + 1
       /\ publishedState' = [publishedState EXCEPT ![n] = newState]
       /\ messages' = messages \cup publishRequests
       /\ UNCHANGED <<appliedState, discoState, term>>


HandleAppendEntriesRequest(n, m) ==
  /\ m.method = AppendEntries
  /\ m.request = TRUE
  /\ IF m.term > term[n]
     THEN
       /\ term' = [term EXCEPT ![n] = m.term]
       /\ discoState' = [discoState EXCEPT ![n] = Follower]
     ELSE
       IF m.term = term[n] /\ discoState[n] \in {Pinging, Become_Master, Become_Follower} /\ Assert(discoState[n] /= Master, "two masters for same term")
       THEN
         /\ discoState' = [discoState EXCEPT ![n] = Follower]
         /\ UNCHANGED <<term>>
       ELSE
         UNCHANGED <<term, discoState>>
  /\ LET
       betterCS == \/ m.state.term > publishedState[n].term
                   \/ /\ m.state.term = publishedState[n].term
                      /\ m.state.version > publishedState[n].version
       response == [method  |-> AppendEntries,
                    request |-> FALSE,
                    source  |-> n,
                    dest    |-> m.source,
                    success |-> TRUE,
                    term    |-> term'[n],
                    version |-> m.state.version]
     IN
       IF
         /\ m.term = term'[n] \* if incoming term was higher, we have adapted to that term
         /\ discoState'[n] = Follower \* we should have converted to follower if incoming term was greater to our term or (equal to our term and we are not Master for that term)
         /\ betterCS
       THEN
         /\ publishedState' = [publishedState EXCEPT ![n] = m.state]
         /\ Reply(response, m)
         /\ UNCHANGED <<appliedState, nextClientValue>>
       ELSE
         /\ Reply([response EXCEPT !.success = FALSE], m)
         /\ UNCHANGED <<appliedState, publishedState, nextClientValue>>


\* apply committed CS to node
HandleApplyRequest(n, m) ==
  /\ m.method = Apply
  /\ m.request = TRUE
  /\ appliedState' = [appliedState EXCEPT ![n] = IF m.state.version > @.version THEN m.state ELSE @]
  /\ Assert(m.state.version > appliedState[n].version => m.state.term >= appliedState[n].term, "seen committed CS with higher version but lower term")
  /\ messages' = messages \ {m}
  /\ UNCHANGED <<publishedState, nextClientValue, discoState, term>>

\* time out and go back to pinging (e.g. node/master fault detection kicks in or waiting on ping responses / append entries responses times out)
Timeout(n) ==
  /\ discoState' = [discoState EXCEPT ![n] = Pinging]
  /\ UNCHANGED <<nextClientValue, publishedState, appliedState, messages, term>>

\* drop request
DropRequest(m) ==
  /\ m.request = TRUE
  /\ messages' = messages \ {m}
  /\ UNCHANGED <<nextClientValue, publishedState, appliedState, discoState, term>>

\* drop response
DropResponse(m) ==
  /\ m.request = FALSE
  /\ messages' = messages \ {m}
  /\ UNCHANGED <<nextClientValue, publishedState, appliedState, discoState, term>>

DropMessagesExcept(sm) ==
  /\ messages' = sm
  /\ UNCHANGED <<nextClientValue, publishedState, appliedState, discoState, term>>

\* handle response with higher term than we currently have
HandleResponseWithHigherTerm(n, m) ==
  /\ m.request = FALSE
  /\ m.method /= Unicast \* term in pinging response could be speculative, ignore it (we actually can look at discoState to decide if it is speculative or not)
  /\ m.term > term[n]
  /\ messages' = messages \ {m}
  /\ term' = [term EXCEPT ![n] = m.term]
  /\ discoState' = [discoState EXCEPT ![n] = Pinging] \* revert to Pinging state
  /\ UNCHANGED <<nextClientValue, publishedState, appliedState>>

\* crash/restart node n (loses ephemeral state)
RestartNode(n) ==
  /\ discoState' = [discoState EXCEPT ![n] = Pinging]
  /\ publishedState' = [publishedState EXCEPT ![n] = [@ EXCEPT !.master = Nil, !.nodes = {n}]]
  /\ appliedState' = [appliedState EXCEPT ![n] = InitialClusterState(n)]
  /\ UNCHANGED <<nextClientValue, messages, term>>

\* next-step relation
Next ==
  \/ \E n \in Nodes : SendPingRequest(n)
  \/ \E m \in messages : HandlePingRequest(m.dest, m)
  \/ \E n \in Nodes : HandlePingResponses(n)
  \/ \E n \in Nodes : HandleJoinRequestsToBecomeMaster(n)
  \/ \E n \in Nodes : HandleJoinRequestWhenMaster(n)
  \/ \E n \in Nodes : CommitState(n)
  \/ \E n \in Nodes : ClientRequest(n)
  \/ \E n \in Nodes : Timeout(n)
  \/ \E m \in messages : HandleAppendEntriesRequest(m.dest, m)
  \/ \E m \in messages : HandleApplyRequest(m.dest, m)
  \/ \E m \in messages : HandleResponseWithHigherTerm(m.dest, m)
  \/ \E m \in messages : DropRequest(m)
  \/ \E m \in messages : DropResponse(m)
  \* \/ \E sm \in SUBSET messages: DropMessagesExcept(sm)
  \/ \E n \in Nodes : RestartNode(n)

----


\* returns true if seq1 is a prefix of seq2
PrefixOf(seq1, seq2) ==
  LET
    len1 == Len(seq1)
    len2 == Len(seq2)
  IN
    len1 <= len2 /\ seq1 = SubSeq(seq2, 1, len1)

\* main invariant:
\* if node n1 has an applied cluster state with version v1 and node n2 has an applied cluster state with version v2:
\*   if v1 <= v2: state1.data must be a prefix of state2.data
\* in particular, when both have the same version, the content must be the same
StateMachineSafety ==
  \A n1, n2 \in Nodes :
    LET
      state1 == appliedState[n1]
      state2 == appliedState[n2]
    IN
      state1.version <= state2.version => PrefixOf(state1.data, state2.data)

OneMasterPerTerm ==
  \A n1, n2 \in Nodes :
    n1 /= n2 /\ discoState[n1] = Master /\ discoState[n2] = Master => term[n1] /= term[n2]

LogMatching ==
  \A n1, n2 \in Nodes :
    /\ publishedState[n1].term = publishedState[n2].term
    /\ publishedState[n1].version = publishedState[n2].version
    => publishedState[n1].data = publishedState[n2].data

NodeTermIsHigherThanCSTerm ==
  \A n \in Nodes : term[n] >= publishedState[n].term


\* State-exploration limits
StateConstraint ==
  /\ nextClientValue <= 4
  /\ \A n \in Nodes: term[n] <= 4
  /\ Cardinality(messages) <= 6
  /\ Cardinality({ m \in messages : m.method = Unicast}) <= 4

====================================================================================================
