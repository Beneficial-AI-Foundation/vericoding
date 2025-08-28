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
lemma ZeroSearchInvariant(a: array<int>, i: int)
  requires forall k :: 0 <= k < a.Length ==> 0 <= a[k]
  requires forall k :: 0 < k < a.Length ==> a[k-1]-1 <= a[k]
  requires 0 <= i < a.Length
  requires a[i] < i
  ensures exists j :: 0 <= j < i && a[j] == 0
{
  if i == 0 {
    assert a[0] < 0;
    assert a[0] >= 0;
    assert false;
  } else {
    if a[i-1] == 0 {
    } else {
      assert a[i-1] >= 1;
      assert a[i-1] - 1 <= a[i];
      assert a[i] >= a[i-1] - 1;
      assert a[i] >= 0;
      assert a[i] < i;
      assert a[i-1] - 1 < i;
      assert a[i-1] < i + 1;
      assert a[i-1] <= i;
      if a[i-1] < i - 1 {
        ZeroSearchInvariant(a, i-1);
      } else {
        assert a[i-1] == i - 1;
        assert a[i] >= a[i-1] - 1 == i - 2;
        assert a[i] < i;
        assert a[i] <= i - 1;
        assert a[i] >= i - 2;
        if i >= 2 && a[i] < i - 1 {
          ZeroSearchInvariant(a, i-1);
        }
      }
    }
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
{
  var i := 0;
  while i < a.Length
    invariant 0 <= i
    invariant forall j :: 0 <= j < i && j < a.Length ==> a[j] != 0
    invariant forall j :: 0 <= j < i && j < a.Length ==> a[j] >= j
  {
    if a[i] == 0 {
      return i;
    }
    if a[i] < i {
      ZeroSearchInvariant(a, i);
      assert exists j :: 0 <= j < i && a[j] == 0;
      assert false;
    }
    assert a[i] >= i;
    assert a[i] != 0;
    var next := a[i];
    assert next >= i;
    assert next != 0;
    assert next > 0;
    if next == i {
      i := i + 1;
    } else {
      i := next;
    }
  }
  return -1;
}
// </vc-code>
