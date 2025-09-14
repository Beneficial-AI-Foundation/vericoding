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
lemma IncreasingProperty(a: array<int>, i: int, j: int)
  requires forall k :: 0 <= k < a.Length ==> 0 <= a[k]
  requires forall k :: 0 < k < a.Length ==> a[k-1]-1 <= a[k]
  requires 0 <= i <= j < a.Length
  ensures a[j] >= a[i] - (j - i)
{
  if i < j {
    IncreasingProperty(a, i, j-1);
    assert a[j-1] >= a[i] - ((j-1) - i);
    assert a[j] >= a[j-1] - 1;
    assert a[j] >= (a[i] - ((j-1) - i)) - 1;
    assert a[j] >= a[i] - (j - i);
  }
}

lemma NoZeroAfterPositive(a: array<int>, i: int)
  requires forall k :: 0 <= k < a.Length ==> 0 <= a[k]
  requires forall k :: 0 < k < a.Length ==> a[k-1]-1 <= a[k]
  requires 0 <= i < a.Length
  requires a[i] > i
  ensures forall j :: 0 <= j <= i ==> a[j] > 0
{
  forall j | 0 <= j <= i
    ensures a[j] > 0
  {
    if j == i {
      assert a[j] == a[i] > i >= 0;
    } else {
      assert j < i;
      IncreasingProperty(a, j, i);
      assert a[i] > i;
      assert a[j] >= a[i] - (i - j);
      assert a[j] >= (i + 1) - (i - j);
      assert a[j] >= j + 1;
      assert a[j] > 0;
    }
  }
}

lemma BoundedGrowth(a: array<int>, i: int)
  requires forall k :: 0 <= k < a.Length ==> 0 <= a[k]
  requires forall k :: 0 < k < a.Length ==> a[k-1]-1 <= a[k]
  requires 0 <= i < a.Length
  requires a[0] == 0
  ensures a[i] <= i
{
  var k := 0;
  while k <= i
    invariant 0 <= k <= i + 1
    invariant forall m :: 0 <= m < k ==> a[m] <= m
  {
    if k == 0 {
      assert a[0] == 0;
      assert a[0] <= 0;
    } else if k < a.Length {
      assert a[k-1] <= k-1 by {
        assert k-1 < k;
        assert 0 <= k-1 < k;
      }
      assert a[k-1] - 1 <= a[k];
      assert a[k] <= a[k-1] + 1;
      assert a[k] <= (k-1) + 1;
      assert a[k] <= k;
    }
    k := k + 1;
  }
  assert a[i] <= i;
}

lemma ExistsZero(a: array<int>, low: int)
  requires forall k :: 0 <= k < a.Length ==> 0 <= a[k]
  requires forall k :: 0 < k < a.Length ==> a[k-1]-1 <= a[k]
  requires a.Length > 0
  requires 0 <= low < a.Length
  requires a[0] == 0
  requires a[low] > 0
  ensures exists j :: 0 <= j < a.Length && a[j] == 0
{
  assert a[0] == 0;
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
  if a.Length == 0 {
    return -1;
  }
  
  if a[0] > 0 {
    NoZeroAfterPositive(a, 0);
    return -1;
  }
  
  // a[0] == 0 since a[0] >= 0 and not a[0] > 0
  assert a[0] == 0;
  
  var low := 0;
  var high := a.Length - 1;
  
  while low < high
    invariant 0 <= low <= high < a.Length
    invariant a[low] <= low
    invariant forall i :: high < i < a.Length ==> a[i] > 0
  {
    var mid := (low + high + 1) / 2;
    
    if a[mid] > mid {
      NoZeroAfterPositive(a, mid);
      high := mid - 1;
    } else {
      low := mid;
    }
  }
  
  if a[low] == 0 {
    return low;
  } else {
    // We have a[0] == 0 and a[low] > 0 (since a[low] != 0 and a[low] >= 0)
    // The sequence must have a zero somewhere
    ExistsZero(a, low);
    
    // Since we did binary search correctly and ended with low == high,
    // and a[low] <= low but a[low] != 0, we must have found a zero
    // This case should not happen given the constraints
    return 0;  // Return the known zero at index 0
  }
}
// </vc-code>

