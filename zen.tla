-------------------------------------------- MODULE zen --------------------------------------------
\* Imported modules used in this specification
EXTENDS Naturals, FiniteSets, Sequences, TLC

\* Set of node ids (all master-eligible nodes)
CONSTANTS Nodes

\* The constant "Nil" denotes a place-holder for a non-existing value
CONSTANTS Nil

CONSTANTS
  Unicast,
  Join,
  AppendEntries,
  Apply

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
VARIABLE votedFor \* used by disco module, persisted
VARIABLE appliedState \* state visible to the other modules on the node

----

\* Return the minimum value from a set, or undefined if the set is empty.
Min(s) == CHOOSE x \in s : \A y \in s : x <= y

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
        /\ votedFor           = [n \in Nodes |-> Nil]

SendPingRequest(n) ==
  /\ discoState[n] = Pinging \* only send pings when in Pinging mode
  /\ LET
       \* send pings to all the nodes (except self), we can still decide later not to act on
       \* some of the ping requests/responses
       pings == {([method  |-> Unicast,
                   request |-> TRUE,
                   source  |-> n,
                   dest    |-> on]) : on \in (Nodes \ {n})}
     IN
       /\ messages' = messages \cup pings
       /\ UNCHANGED <<nextClientValue, publishedState, appliedState, term, discoState, votedFor>>

HandlePingRequest(n, m) ==
  /\ m.method = Unicast
  /\ m.request = TRUE
  /\ LET
       response == [method  |-> Unicast,
                    request |-> FALSE,
                    source  |-> n,
                    dest    |-> m.source,
                    master  |-> IF discoState[n] \in {Master, Follower} THEN publishedState[n].master ELSE Nil,
                    version |-> publishedState[n].version,
                    csTerm  |-> publishedState[n].term,
                    term    |-> term[n],
                    discoSt |-> discoState[n]]
     IN
       /\ Reply(response, m)
       /\ UNCHANGED <<nextClientValue, publishedState, appliedState, term, discoState, votedFor>>

\* when node is in pinging mode, check ping responses to determine if it should become master or follower
HandlePingResponses(n) ==
  /\ discoState[n] = Pinging
  /\ LET
       pingResponses == { ms \in messages : ms.method = Unicast /\ ms.request = FALSE /\ ms.dest = n }
       activeMastersWithBetterTerm == { pr \in pingResponses :
         /\ pr.master /= Nil
         /\ pr.master /= n
         /\ \/ pr.term > term[n] \* master has a higher term than us
            \/ /\ pr.term = term[n] \* same term than us, but we voted for that same master (or did not vote yet), simply rejoin
               /\ votedFor[n] \in {pr.source, Nil}
       }
       masterCandidates == {[node |-> pr.source,
                             version |-> pr.version,
                             csTerm |-> pr.csTerm,
                             term |-> pr.term,
                             discoSt |-> pr.discoSt] : pr \in pingResponses} \cup
                           {[node |-> n,
                             version |-> publishedState[n].version,
                             csTerm |-> publishedState[n].term,
                             term |-> term[n],
                             discoSt |-> discoState[n]]}
     IN
       IF Cardinality(activeMastersWithBetterTerm) > 0
       THEN
         LET
           masterToJoin == CHOOSE pr \in activeMastersWithBetterTerm : TRUE \* just chose any of them
           \* choose master's term as current term and vote for it, send join request
           joinRequest == [method  |-> Join,
                           request |-> TRUE,
                           source  |-> n,
                           dest    |-> masterToJoin.master,
                           term    |-> masterToJoin.term]
         IN
           /\ messages' = (messages \ pingResponses) \cup { joinRequest }
           /\ discoState' = [discoState EXCEPT ![n] = Become_Follower]
           /\ term' = [term EXCEPT ![n] = masterToJoin.term]
           /\ votedFor' = [votedFor EXCEPT ![n] = n]
           /\ UNCHANGED <<nextClientValue, publishedState, appliedState>>
       ELSE
         IF Cardinality({pr.node : pr \in masterCandidates}) < MinMasterNodes
         THEN
           /\ messages' = messages \ pingResponses
           /\ UNCHANGED <<nextClientValue, publishedState, appliedState, term, discoState, votedFor>>
         ELSE
           LET
             \* choose the node with the best cluster state
             bestCSNode == (CHOOSE pr \in masterCandidates : \A pr2 \in masterCandidates :
               pr.csTerm > pr2.csTerm \/ (pr.csTerm = pr2.csTerm /\ pr.version >= pr2.version)).node
             \* choose highest term seen + 1. If node is becoming master or follower, it already has a speculative term
             nextTerm == Max({ IF pr.discoSt \in {Become_Master, Become_Follower} THEN pr.term ELSE pr.term + 1 : pr \in masterCandidates })
             joinRequest == [method  |-> Join,
                             request |-> TRUE,
                             source  |-> n,
                             dest    |-> bestCSNode,
                             term    |-> nextTerm]
           IN
             IF bestCSNode = n
             THEN
               /\ messages' = messages \ pingResponses
               /\ discoState' = [discoState EXCEPT ![n] = Become_Master]
               /\ term' = [term EXCEPT ![n] = nextTerm]
               /\ votedFor' = [votedFor EXCEPT ![n] = n]
               /\ UNCHANGED <<nextClientValue, publishedState, appliedState>>
             ELSE
               /\ messages' = (messages \ pingResponses) \cup { joinRequest }
               /\ discoState' = [discoState EXCEPT ![n] = Become_Follower]
               /\ term' = [term EXCEPT ![n] = nextTerm]
               /\ votedFor' = [votedFor EXCEPT ![n] = bestCSNode]
               /\ UNCHANGED <<nextClientValue, publishedState, appliedState>>

\* node n wants to become master and checks if it has received enough joins or
\* node n is master and lets another node join
HandleJoinRequest(n) ==
  /\ discoState[n] \in {Become_Master, Master}
  /\ LET
       joinRequests == { m \in messages : m.method = Join /\ m.request /\ m.dest = n }
       sameTermJoins == { m \in joinRequests : m.term = term[n] }
       voteGrantingNodes == { m.source : m \in sameTermJoins }
       newState == [publishedState[n] EXCEPT !.master = n, !.nodes = @ \cup voteGrantingNodes, !.term = term[n], !.version = @ + 1, !.data = Append(@, nextClientValue)]
       publishRequests == { [method  |-> AppendEntries,
                             request |-> TRUE,
                             source  |-> n,
                             dest    |-> ns,
                             term    |-> term[n],
                             state   |-> newState] : ns \in (newState.nodes \ {n}) }
     IN
       /\ IF discoState[n] = Become_Master 
          THEN Cardinality(voteGrantingNodes) + 1 >= MinMasterNodes \* +1 as we don't send a vote request to ourselves
          ELSE TRUE \* if we're already master, no need to check this condition
       /\ discoState' = [discoState EXCEPT ![n] = Master]
       /\ publishedState' = [publishedState EXCEPT ![n] = newState]
       /\ nextClientValue' = nextClientValue + 1
       /\ messages' = (messages \ joinRequests) \cup publishRequests
       /\ UNCHANGED <<appliedState, term, votedFor>>

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
    /\ UNCHANGED <<nextClientValue, discoState, publishedState, term, votedFor>>


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
       /\ UNCHANGED <<appliedState, discoState, term, votedFor>>


HandleAppendEntriesRequest(n, m) ==
  /\ m.method = AppendEntries
  /\ m.request = TRUE
  /\ IF m.term > term[n]
     THEN
       /\ term' = [term EXCEPT ![n] = m.term]
       /\ discoState' = [discoState EXCEPT ![n] = Follower]
       /\ votedFor' = [votedFor EXCEPT ![n] = Nil]
     ELSE
       IF m.term = term[n] /\ discoState[n] \in {Pinging, Become_Master, Become_Follower}
       THEN
         /\ discoState' = [discoState EXCEPT ![n] = Follower]
         /\ UNCHANGED <<term, votedFor>>
       ELSE
         UNCHANGED <<term, discoState, votedFor>>
  /\ LET
       success == \/ m.term > publishedState[n].term
                  \/ /\ m.term = publishedState[n].term
                     /\ m.state.version > publishedState[n].version 
       response == [method  |-> AppendEntries,
                    request |-> FALSE,
                    source  |-> n,
                    dest    |-> m.source,
                    success |-> success,
                    term    |-> term'[n],
                    version |-> m.state.version]
     IN
       \* fail request
       \/ /\ \/ m.term < term'[n]
             \/ /\ m.term = term'[n]
                /\ discoState'[n] = Follower
                /\ \lnot success
          /\ Reply([response EXCEPT !.success = FALSE], m)
          /\ UNCHANGED <<appliedState, publishedState, nextClientValue>>
       \* successful request
       \/ /\ m.term = term'[n]
          /\ discoState'[n] = Follower
          /\ success
          /\ publishedState' = [publishedState EXCEPT ![n] = m.state]
          /\ Reply(response, m)
          /\ UNCHANGED <<appliedState, nextClientValue>>


\* apply committed CS to node
HandleApplyRequest(n, m) ==
  /\ m.method = Apply
  /\ m.request = TRUE
  /\ appliedState' = [appliedState EXCEPT ![n] = IF m.state.version > @.version THEN m.state ELSE @]
  /\ messages' = messages \ {m}
  /\ UNCHANGED <<publishedState, nextClientValue, votedFor, discoState, term>>

\* time out and go back to pinging (e.g. node/master fault detection kicks in)
Timeout(n) ==
  /\ discoState' = [discoState EXCEPT ![n] = Pinging]
  /\ UNCHANGED <<nextClientValue, publishedState, appliedState, messages, term, votedFor>>

\* drop request
DropRequest(m) ==
  /\ m.request = TRUE
  /\ messages' = messages \ {m}
  /\ UNCHANGED <<nextClientValue, publishedState, appliedState, discoState, term, votedFor>>

\* drop response
DropResponse(m) ==
  /\ m.request = FALSE
  /\ messages' = messages \ {m}
  /\ UNCHANGED <<nextClientValue, publishedState, appliedState, discoState, term, votedFor>>

\* handle response with higher term than we currently have
HandleResponseWithHigherTerm(n, m) ==
  /\ m.request = FALSE
  /\ m.method /= Unicast \* term in pinging response is speculative, ignore it
  /\ m.term > term[n]
  /\ messages' = messages \ {m}
  /\ term' = [term EXCEPT ![n] = m.term]
  /\ discoState' = [discoState EXCEPT ![n] = Pinging]
  /\ votedFor' = [votedFor EXCEPT ![n] = Nil]
  /\ UNCHANGED <<nextClientValue, publishedState, appliedState>>

\* crash/restart node n
RestartNode(n) ==
  /\ discoState' = [discoState EXCEPT ![n] = Pinging]
  /\ publishedState' = [publishedState EXCEPT ![n] = [@ EXCEPT !.master = Nil, !.nodes = {n}]]
  /\ appliedState' = [appliedState EXCEPT ![n] = InitialClusterState(n)]
  /\ UNCHANGED <<nextClientValue, messages, term, votedFor>>

\* next-step relation
Next ==
  \/ \E n \in Nodes : SendPingRequest(n)
  \/ \E m \in messages : HandlePingRequest(m.dest, m)
  \/ \E n \in Nodes : HandlePingResponses(n)
  \/ \E n \in Nodes : HandleJoinRequest(n)
  \/ \E n \in Nodes : CommitState(n)
  \/ \E n \in Nodes : ClientRequest(n)
  \/ \E n \in Nodes : Timeout(n)
  \/ \E m \in messages : HandleAppendEntriesRequest(m.dest, m)
  \/ \E m \in messages : HandleApplyRequest(m.dest, m)
  \/ \E m \in messages : HandleResponseWithHigherTerm(m.dest, m)
  \/ \E m \in messages : DropRequest(m)
  \/ \E m \in messages : DropResponse(m)
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

====================================================================================================
