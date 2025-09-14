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
lemma NoZeroBetween(a: array<int>, i: int)
  requires forall j :: 0 <= j < a.Length ==> 0 <= a[j]
  requires forall j :: 0 < j < a.Length ==> a[j-1]-1 <= a[j]
  requires 0 <= i < a.Length
  requires a[i] > i
  ensures forall k :: i < k < a.Length && k < a[i] ==> a[k] != 0
{
  if a[i] <= i + 1 {
    return;
  }
  
  var j := i + 1;
  while j < a.Length && j < a[i]
    invariant i < j <= a[i]
    invariant j <= a.Length
    invariant forall k :: i < k < j ==> a[k] != 0
    invariant forall k :: i <= k < j ==> a[k] >= k
  {
    assert i < j;
    assert a[i] >= i;
    assert a[i] > i;
    
    if j > i + 1 {
      var m := i;
      while m < j - 1
        invariant i <= m <= j - 1
        invariant a[m] >= m
      {
        assert m + 1 < j;
        assert 0 < m + 1 < a.Length;
        assert a[m] - 1 <= a[m + 1];
        assert a[m + 1] >= a[m] - 1 >= m - 1;
        assert a[m + 1] >= m + 1 - 2;
        m := m + 1;
      }
    }
    
    if j > 0 && j - 1 >= i {
      assert a[j-1] >= j-1;
    }
    
    if j < a.Length {
      assert a[j] >= a[j-1] - 1;
      assert a[j] >= (j-1) - 1;
      assert a[j] >= j - 2;
      
      if a[j] == 0 {
        assert 0 >= j - 2;
        assert j <= 2;
        assert j >= i + 1;
        assert i <= 1;
        
        if i == 0 {
          assert j == 1 || j == 2;
          if j == 1 {
            assert a[1] >= a[0] - 1 > 0 - 1;
            assert false;
          }
        } else if i == 1 {
          assert j == 2;
          assert a[2] >= a[1] - 1 > 1 - 1;
          assert false;
        }
      }
    }
    j := j + 1;
  }
}
// </vc-helpers>

// <vc-spec>
method FindZero(a: array<int>) returns (index: int)
  requires forall i :: 0 <= i < a.Length ==> 0 <= a[i]
  requires forall i :: 0 < i < a.Length ==> a[i-1]-1 <= a[i]
  ensures index < 0  ==> forall i :: 0 <= i < a.Length ==> a[i] != 0
  ensures 0 <= index ==> index < a.Length && a[index] == 0
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> a[k] != 0
  {
    if a[i] == 0 {
      return i;
    } else if a[i] > i {
      NoZeroBetween(a, i);
      var next_i := a[i];
      if next_i <= a.Length {
        i := next_i;
      } else {
        i := i + 1;
      }
    } else {
      i := i + 1;
    }
  }
  return -1;
}
// </vc-code>

