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
  Commit, \* only request is modeled
  Catchup \* only response is modeled

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
VARIABLE currentConfiguration
VARIABLE currentClusterState
VARIABLE lastAcceptedTerm
VARIABLE lastAcceptedValue
VARIABLE joinVotes
VARIABLE electionWon
VARIABLE electionValueForced
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
        /\ currentConfiguration \in {[n \in Nodes |-> vc] : vc \in ValidConfigs} \* all agree on initial config
        /\ currentClusterState \in {[n \in Nodes |-> v] : v \in Values} \* all agree on initial value
        /\ lastAcceptedTerm = [n \in Nodes |-> Nil]
        /\ lastAcceptedValue = [n \in Nodes |-> Nil]
        /\ joinVotes = [n \in Nodes |-> {}]
        /\ electionWon = [n \in Nodes |-> FALSE]
        /\ electionValueForced = [n \in Nodes |-> FALSE]
        /\ publishPermitted = [n \in Nodes |-> FALSE]

\* Send join request from node n to node nm for term t
HandleStartJoin(n, nm, t) ==
  /\ t > currentTerm[n]
  /\ (lastAcceptedTerm[n] /= Nil => t > lastAcceptedTerm[n]) 
  /\ LET
       joinRequest == [method  |-> Join,
                       source  |-> n,
                       dest    |-> nm,
                       slot    |-> firstUncommittedSlot[n],
                       term    |-> t,
                       laTerm  |-> lastAcceptedTerm[n]]
     IN
       /\ currentTerm' = [currentTerm EXCEPT ![n] = t]
       /\ publishPermitted' = [publishPermitted EXCEPT ![n] = TRUE]
       /\ electionWon' = [electionWon EXCEPT ![n] = FALSE]
       /\ electionValueForced' = [electionValueForced EXCEPT ![n] = FALSE]
       /\ joinVotes' = [joinVotes EXCEPT ![n] = {}]
       /\ messages' = messages \cup { joinRequest }
       /\ UNCHANGED <<currentClusterState, currentConfiguration,
                      firstUncommittedSlot, lastAcceptedValue, lastAcceptedTerm>>

\* node n wants to become master and checks if it has received enough joins (= votes) for its term
HandleJoinRequest(n, m, rcvrs) ==
  /\ m.method = Join
  /\ m.term = currentTerm[n]
  /\ \/ /\ m.slot < firstUncommittedSlot[n]
     \/ /\ m.slot = firstUncommittedSlot[n]
        /\ \/ m.laTerm = Nil
           \/ m.laTerm = lastAcceptedTerm[n]
           \/ /\ m.laTerm /= Nil
              /\ lastAcceptedTerm[n] /= Nil
              /\ m.laTerm <= lastAcceptedTerm[n]
              /\ electionValueForced[n]
  /\ joinVotes' = [joinVotes EXCEPT ![n] = @ \cup { m.source }]
  /\ electionValueForced' = [electionValueForced EXCEPT ![n] = @ \/ (m.laTerm /= Nil /\ m.slot = firstUncommittedSlot[n])]
  /\ electionWon' = [electionWon EXCEPT ![n] = IsQuorum(joinVotes'[n], currentConfiguration[n])]
  /\ IF electionValueForced'[n] /\ electionWon'[n] /\ \lnot electionWon[n]
     THEN LET publishRequests == { [method  |-> Publish,
                                    request |-> TRUE,
                                    source  |-> n,
                                    dest    |-> ns,
                                    term    |-> currentTerm[n],
                                    slot    |-> firstUncommittedSlot[n],
                                    value   |-> lastAcceptedValue[n]] : ns \in rcvrs }
     IN
       /\ messages' = (messages \ {m}) \cup (IF electionValueForced'[n] /\ electionWon'[n] /\ \lnot electionWon[n] THEN publishRequests ELSE {})
       /\ publishPermitted' = [publishPermitted EXCEPT ![n] = FALSE]
     ELSE
       /\ messages' = (messages \ {m})
       /\ UNCHANGED <<publishPermitted>>
  /\ UNCHANGED <<currentClusterState, currentConfiguration, currentTerm,
                 firstUncommittedSlot, lastAcceptedValue, lastAcceptedTerm>>

\* node n (which is master) instructs other nodes to commit change
CommitState(n, rcvrs) ==
  LET
    publishResponses == { m \in messages :
                            /\ m.method = Publish
                            /\ m.request = FALSE
                            /\ m.dest = n
                            /\ m.term = currentTerm[n]
                            /\ m.slot = firstUncommittedSlot[n] }
    successResponses == { pr \in publishResponses : pr.success }
    successNodes == { pr.source : pr \in successResponses }
    commitRequests == { [method  |-> Commit,
                         source  |-> n,
                         dest    |-> ns,
                         term    |-> currentTerm[n],
                         slot    |-> firstUncommittedSlot[n]] : ns \in rcvrs }
  IN
    /\ IsQuorum(successNodes, currentConfiguration[n])
    /\ messages' = (messages \ publishResponses) \cup commitRequests
    /\ UNCHANGED <<currentClusterState, currentConfiguration, currentTerm, electionWon, electionValueForced,
                   firstUncommittedSlot, lastAcceptedValue, lastAcceptedTerm, publishPermitted, joinVotes>>


ClientRequest(n, v, rcvrs) ==
  /\ electionWon[n]
  /\ publishPermitted[n]
  /\ electionValueForced[n] = FALSE
  /\ LET
       publishRequests == { [request |-> TRUE,
                             method  |-> Publish,
                             source  |-> n,
                             dest    |-> ns,
                             term    |-> currentTerm[n],
                             slot    |-> firstUncommittedSlot[n],
                             value   |-> [type |-> ApplyCSDiff, 
                                          val  |-> (currentClusterState[n] :> v)]
                            ] : ns \in rcvrs }
     IN
       /\ publishPermitted' = [publishPermitted EXCEPT ![n] = FALSE]
       /\ messages' = messages \cup publishRequests
       /\ UNCHANGED <<currentClusterState, currentConfiguration, currentTerm, electionWon, electionValueForced,
                      firstUncommittedSlot, lastAcceptedValue, lastAcceptedTerm, joinVotes>>


HandlePublishRequest(n, m) ==
  /\ m.method = Publish
  /\ m.request = TRUE
  /\ m.slot = firstUncommittedSlot[n]
  /\ m.term = currentTerm[n]
  /\ lastAcceptedTerm' = [lastAcceptedTerm EXCEPT ![n] = m.term]
  /\ lastAcceptedValue' = [lastAcceptedValue EXCEPT ![n] = m.value]
  /\ LET
       response == [method  |-> Publish,
                    request |-> FALSE,
                    source  |-> n,
                    dest    |-> m.source,
                    success |-> TRUE,
                    term    |-> m.term,
                    slot    |-> m.slot]
     IN
       /\ Reply(response, m)
       /\ UNCHANGED <<currentClusterState, currentConfiguration, currentTerm, electionValueForced,
                      electionWon, firstUncommittedSlot, publishPermitted, joinVotes>>

ChangeVoters(n, vs, rcvrs) ==
  /\ electionWon[n]
  /\ publishPermitted[n]
  /\ electionValueForced[n] = FALSE
  /\ LET
       publishRequests == { [request |-> TRUE,
                             method  |-> Publish,
                             source  |-> n,
                             dest    |-> ns,
                             term    |-> currentTerm[n],
                             slot    |-> firstUncommittedSlot[n],
                             value   |-> [type |-> Reconfigure, val |-> vs]] : ns \in rcvrs }
     IN
       /\ publishPermitted' = [publishPermitted EXCEPT ![n] = FALSE]
       /\ messages' = messages \cup publishRequests
       /\ UNCHANGED <<currentClusterState, currentConfiguration, currentTerm, electionValueForced,
                      electionWon, firstUncommittedSlot, lastAcceptedValue, lastAcceptedTerm, joinVotes>> 

\* apply committed CS to node
HandleCommitRequest(n, m) ==
  /\ m.method = Commit
  /\ m.slot = firstUncommittedSlot[n]
  /\ m.term = lastAcceptedTerm[n] 
  /\ firstUncommittedSlot' = [firstUncommittedSlot EXCEPT ![n] = @ + 1]
  /\ lastAcceptedTerm' = [lastAcceptedTerm EXCEPT ![n] = Nil]
  /\ lastAcceptedValue' = [lastAcceptedValue EXCEPT ![n] = Nil]
  /\ publishPermitted' = [publishPermitted EXCEPT ![n] = TRUE]
  /\ electionValueForced' = [electionValueForced EXCEPT ![n] = FALSE]
  /\ IF lastAcceptedValue[n].type = Reconfigure THEN
       /\ currentConfiguration' = [currentConfiguration EXCEPT ![n] = lastAcceptedValue[n].val]
       /\ electionWon' = [electionWon EXCEPT ![n] = IsQuorum(joinVotes[n], currentConfiguration'[n])]
       /\ UNCHANGED <<currentClusterState>>
     ELSE
       /\ Assert(lastAcceptedValue[n].type = ApplyCSDiff, "unexpected type")
       /\ Assert(DOMAIN(lastAcceptedValue[n].val) = {currentClusterState[n]}, "diff mismatch")
       /\ currentClusterState' = [currentClusterState EXCEPT ![n] = lastAcceptedValue[n].val[@]] \* apply diff
       /\ UNCHANGED <<currentConfiguration, electionWon>> 
  /\ messages' = messages \ {m}
  /\ UNCHANGED <<currentTerm, joinVotes>>

\* node n captures current state and sends a catch up message (giving other nodes a chance to catchup)
SendCatchupResponse(n) ==
  /\ LET
       catchupMessage == [method  |-> Catchup,
                          slot    |-> firstUncommittedSlot[n],
                          config  |-> currentConfiguration[n],
                          state   |-> currentClusterState[n]]
     IN
       /\ messages' = messages \cup { catchupMessage }
       /\ UNCHANGED <<currentClusterState, currentConfiguration, currentTerm, electionValueForced, lastAcceptedValue,
                      electionWon, firstUncommittedSlot, publishPermitted, joinVotes, lastAcceptedTerm>>

\* node n handles a catchup message
HandleCatchupResponse(n, m) ==
  /\ m.method = Catchup
  /\ m.slot > firstUncommittedSlot[n]
  /\ firstUncommittedSlot' = [firstUncommittedSlot EXCEPT ![n] = m.slot]
  /\ lastAcceptedTerm' = [lastAcceptedTerm EXCEPT ![n] = Nil]
  /\ lastAcceptedValue' = [lastAcceptedValue EXCEPT ![n] = Nil]
  /\ publishPermitted' = [publishPermitted EXCEPT ![n] = FALSE]
  /\ electionWon' = [electionWon EXCEPT ![n] = FALSE]
  /\ electionValueForced' = [electionValueForced EXCEPT ![n] = FALSE]
  /\ currentConfiguration' = [currentConfiguration EXCEPT ![n] = m.config]
  /\ currentClusterState' = [currentClusterState EXCEPT ![n] = m.state]
  /\ joinVotes' = [joinVotes EXCEPT ![n] = {}]
  /\ UNCHANGED <<currentTerm, messages>>
  

\* drop request or response
DropMessage(m) ==
  /\ messages' = messages \ {m}
  /\ UNCHANGED <<currentClusterState, currentConfiguration, currentTerm, electionWon, electionValueForced,
                 firstUncommittedSlot, lastAcceptedValue, lastAcceptedTerm, publishPermitted, joinVotes>>

\* crash/restart node n (loses ephemeral state)
RestartNode(n) ==
  /\ electionWon' = [electionWon EXCEPT ![n] = FALSE]
  /\ publishPermitted' = [publishPermitted EXCEPT ![n] = FALSE]
  /\ joinVotes' = [joinVotes EXCEPT ![n] = {}]
  /\ electionValueForced' = [electionValueForced EXCEPT ![n] = FALSE]
  /\ UNCHANGED <<messages, firstUncommittedSlot, currentTerm, currentConfiguration, 
                 currentClusterState, lastAcceptedTerm, lastAcceptedValue>>

\* next-step relation
Next ==
  \/ \E n, nm \in Nodes : HandleStartJoin(n, nm, currentTerm[n] + 1)
  \/ \E m \in messages : \E ns \in SUBSET(Nodes) : HandleJoinRequest(m.dest, m, ns)
  \/ \E n \in Nodes : \E ns \in SUBSET(Nodes) : CommitState(n, ns)
  \/ \E n \in Nodes : \E ns \in SUBSET(Nodes) : \E v \in Values : ClientRequest(n, v, ns)
  \/ \E m \in messages : HandlePublishRequest(m.dest, m)
  \/ \E m \in messages : HandleCommitRequest(m.dest, m)
  \/ \E m \in messages : DropMessage(m)
  \/ \E n \in Nodes : RestartNode(n)
  \/ \E n \in Nodes : \E ns \in SUBSET(Nodes) : \E vs \in ValidConfigs : ChangeVoters(n, vs, ns)
  \/ \E n \in Nodes : SendCatchupResponse(n)
  \/ \E n \in Nodes : \E m \in messages : HandleCatchupResponse(n, m)

----

\* main invariant:
StateMachineSafety ==
  \A n1, n2 \in Nodes :
    firstUncommittedSlot[n1] = firstUncommittedSlot[n2] => 
      /\ currentClusterState[n1] = currentClusterState[n2]
      /\ currentConfiguration[n1] = currentConfiguration[n2]

OneMasterPerTerm ==
  \A n1, n2 \in Nodes :
    n1 /= n2 /\ electionWon[n1] /\ electionWon[n2] => 
      \/ currentTerm[n1] /= currentTerm[n2] 
      \/ currentConfiguration[n1] /= currentConfiguration[n2]

LogMatching ==
  \A n1, n2 \in Nodes :
    /\ firstUncommittedSlot[n1] = firstUncommittedSlot[n2]
    /\ lastAcceptedTerm[n1] = lastAcceptedTerm[n2]
    => lastAcceptedValue[n1] = lastAcceptedValue[n2]

\* State-exploration limits
StateConstraint ==
  /\ \A n \in Nodes: currentTerm[n] <= 3
  /\ \A n \in Nodes: firstUncommittedSlot[n] <= 2
  /\ Cardinality(messages) <= 4

====================================================================================================
