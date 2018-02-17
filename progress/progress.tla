\* Use the following model settings:
\*   Temporal formula: Spec
\*   Invariants: Correctness
\*   Properties: Liveness
\*
\* You can use N=3 and Quorum=2 as sound values for the model constants
------------------------------ MODULE progress ------------------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC
CONSTANT N, Quorum
ASSUME N \in Nat /\ N > 0
ASSUME Quorum <= N
Nodes == 1..N

(* --algorithm progress
variable
  \* The progress set of each Cassandra node
  progress = [n \in Nodes |-> {}],
  \* Message queue
  queue = <<"first step", "second step">>,
  \* How many progress handlers have seen the switch from unprocessed to processed
  switchHappened = 0,
  \* The number of unacknowledged messages
  unacked = 0;

define
  \* Whether the given set of statuses is considered "processing complete"
  ProcessingComplete(p) == p = {"first step", "second step"}
  \* Reads the progress set from the given nodes
  ReadProgress(nodes) == UNION {progress[n] : n \in nodes}
  \* Returs a set with all subsets of nodes with the given cardinality
  NNodes(n) == {x \in SUBSET Nodes : Cardinality(x) = n}
end define

\* Receive a message from the queue
macro recv(queue, receiver)
begin
  await queue /= <<>>;
  receiver := Head(queue);
  queue := Tail(queue);
end macro

\* Appends status to the progress set at Quorum nodes
procedure appendProgress(writeNodes, status)
variable nodes = writeNodes;
begin P0:
  while nodes # {} do
  P1:
    with n \in nodes do
      progress[n] := progress[n] \union {status};
      nodes := nodes \ {n};
    end with
  end while;
  return;
end procedure

\* Handles a progress message from the queue
fair process progressHandler \in {"handler1", "handler2"}
variable
  writeQuorumNodes \in NNodes(Quorum),
  readQuorumNodes \in NNodes(Quorum),
  secondReadQuorumNodes \in NNodes(Quorum),
  completedBefore = FALSE,
  message = "";
begin P0:
  while TRUE do
  Poll:
    recv(queue, message);
    unacked := unacked + 1;
  Read:
    completedBefore := ProcessingComplete(ReadProgress(readQuorumNodes));
  Write:
    call appendProgress(writeQuorumNodes, message);
  ReadAfterWrite:
    if ~completedBefore /\ ProcessingComplete(ReadProgress(secondReadQuorumNodes)) then
      \* The real progress handler would trigger some real action here of course
      switchHappened := switchHappened + 1;
    end if;
  Ack:
    unacked := unacked - 1;
  end while;
end process;

end algorithm *)
\* BEGIN TRANSLATION
\* END TRANSLATION

Correctness == \/ queue # <<>>
               \/ unacked > 0
               \/ switchHappened > 0
Liveness == <>[](switchHappened > 0)
NoDupAck == unacked >= 0
\* Note that this cannot be guaranteed with the current implementation
NoDupSwitch == switchHappened <= 1

=============================================================================
