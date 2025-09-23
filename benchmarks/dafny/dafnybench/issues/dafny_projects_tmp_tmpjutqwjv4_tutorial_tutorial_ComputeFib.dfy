// <vc-preamble>
// Working through https://dafny.org/dafny/OnlineTutorial/guide

function fib(n: nat): nat
{
  if n == 0 then 0
  else if n == 1 then 1
  else fib(n - 1) + fib(n - 2)
}
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method ComputeFib(n: nat) returns (ret: nat)
  ensures ret == fib(n)
// </vc-spec>
// <vc-code>
{
  var a := 0;
  var b := 1;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant a == fib(i)
    invariant b == fib(i+1)
  {
    a, b := b, a+b;
    i := i + 1;
  }
  assert i == n;

  return a;
}
// </vc-code>

predicate sorted(a: array<int>)
  reads a
{
  forall n, m :: 0 <= n < m < a.Length ==> a[n] <= a[m]
}



// https://dafny.org/dafny/OnlineTutorial/ValueTypes

function update(s: seq<int>, i: int, v: int): seq<int>
  requires 0 <= i < |s|
  ensures update(s, i, v) == s[i := v]
{
  s[..i] + [v] + s[i+1..]
}


// https://dafny.org/dafny/OnlineTutorial/Lemmas

lemma SkippingLemma(a: array<int>, j: int)
  requires forall i :: 0 <= i < a.Length ==> 0 <= a[i]
  requires forall i :: 0 < i < a.Length ==> a[i-1]-1 <= a[i]
  requires 0 <= j < a.Length
  ensures forall i :: j <= i < j + a[j] && i < a.Length ==> a[i] != 0
{
  var i := j;
  while i < j + a[j] && i < a.Length
    invariant i < a.Length ==> a[i] >= a[j] - (i-j)
    invariant forall k :: j <= k < i && k < a.Length ==> a[k] != 0
  {
    i := i + 1;
  }
}



function count(a: seq<bool>): nat
{
  if |a| == 0 then 0 else
  (if a[0] then 1 else 0) + count(a[1..])
}

lemma DistributiveLemma(a: seq<bool>, b: seq<bool>)
  ensures count(a + b) == count(a) + count(b)
{
  if a == [] {
    assert a+b == b;
  } else {
    // Unnecessary! DistributiveLemma(a[1..], b);
    assert a + b == [a[0]] + (a[1..] + b);
  }
}


class Node
{
  var next: seq<Node>
}
predicate closed(graph: set<Node>)
  reads graph
{
  forall i :: i in graph ==> forall k :: 0 <= k < |i.next| ==> i.next[k] in graph && i.next[k] != i
}
predicate path(p: seq<Node>, graph: set<Node>)
  requires closed(graph) && 0 < |p|
  reads graph
{
  p[0] in graph &&
    (|p| > 1 ==> p[1] in p[0].next && // the first link is valid, if it exists
     path(p[1..], graph)) // and the rest of the sequence is a valid
}
predicate pathSpecific(p: seq<Node>, start: Node, end: Node, graph: set<Node>)
  requires closed(graph)
  reads graph
{
  0 < |p| && // path is nonempty
  start == p[0] && end == p[|p|-1] && // it starts and ends correctly
  path(p, graph) // and it is a valid path
}

lemma DisproofLemma(p: seq<Node>, subgraph: set<Node>,
                    root: Node, goal: Node, graph: set<Node>)
  requires closed(subgraph) && closed(graph) && subgraph <= graph
  requires root in subgraph && goal in graph - subgraph
  ensures !pathSpecific(p, root, goal, graph)
{
  if |p| >= 2 && p[0] == root && p[1] in p[0].next {
    DisproofLemma(p[1..], subgraph, p[1], goal, graph);
  }
}

lemma ClosedLemma(subgraph: set<Node>, root: Node, goal: Node, graph: set<Node>)
  requires closed(subgraph) && closed(graph) && subgraph <= graph
  requires root in subgraph && goal in graph - subgraph
  ensures !(exists p: seq<Node> :: pathSpecific(p, root, goal, graph))
{
  forall p { DisproofLemma(p, subgraph, root, goal, graph); }
}