// Working through https://dafny.org/dafny/OnlineTutorial/guide

function fib(n: nat): nat
{
  if n == 0 then 0
  else if n == 1 then 1
  else fib(n - 1) + fib(n - 2)
}


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

function count(a: seq<bool>): nat
{
  if |a| == 0 then 0 else
  (if a[0] then 1 else 0) + count(a[1..])
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

// <vc-helpers>
lemma BinarySearchHelper(a: array<int>, lo: int, hi: int)
  requires 0 <= lo <= hi <= a.Length
  requires forall i :: 0 <= i < a.Length ==> 0 <= a[i]
  requires forall i :: 0 < i < a.Length ==> a[i-1] <= a[i] + 1
  ensures forall i :: 0 <= i < lo ==> a[i] != 0
  ensures forall i :: hi <= i < a.Length ==> a[i] != 0
{
  var i := 0;
  while i < lo
    invariant 0 <= i <= lo
    invariant forall j :: 0 <= j < i ==> a[j] != 0
  {
    if a[i] == 0 {
      assert false;
    }
    i := i + 1;
  }
  
  i := hi;
  while i < a.Length
    invariant hi <= i <= a.Length
    invariant forall j :: i <= j < a.Length ==> a[j] != 0
  {
    if a[i] == 0 {
      assert false;
    }
    i := i + 1;
  }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method FindZero(a: array<int>) returns (index: int)
  requires forall i :: 0 <= i < a.Length ==> 0 <= a[i]
  requires forall i :: 0 < i < a.Length ==> a[i-1]-1 <= a[i]
  ensures index < 0  ==> forall i :: 0 <= i < a.Length ==> a[i] != 0
  ensures 0 <= index ==> index < a.Length && a[index] == 0
// </vc-spec>
// </vc-spec>

// <vc-code>
method FindZeroImpl(a: array<int>) returns (index: int)
  requires forall i :: 0 <= i < a.Length ==> 0 <= a[i]
  requires forall i :: 0 < i < a.Length ==> a[i-1] <= a[i] + 1
  ensures index < 0 ==> forall i :: 0 <= i < a.Length ==> a[i] != 0
  ensures 0 <= index ==> index < a.Length && a[index] == 0
{
  var lo := 0;
  var hi := a.Length;
  
  while lo < hi
    invariant 0 <= lo <= hi <= a.Length
    invariant forall i :: 0 <= i < lo ==> a[i] != 0
    invariant forall i :: hi <= i < a.Length ==> a[i] != 0
  {
    var mid := (lo + hi) / 2;
    if a[mid] == 0 {
      index := mid;
      return;
    } else if a[mid] < 0 {
      hi := mid;
    } else {
      lo := mid + 1;
    }
  }
  index := -1;
  return;
}
// </vc-code>
