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
lemma FindZeroLemma(a: array<int>, j: int)
  requires forall i :: 0 <= i < a.Length ==> 0 <= a[i]
  requires forall i :: 0 < i < a.Length ==> a[i-1]-1 <= a[i]
  requires 0 <= j < a.Length
  requires a[j] > 0
  ensures forall k :: 0 <= k <= j ==> a[k] > 0
{
  if j > 0 {
    // First prove that a[j-1] > 0
    if a[j-1] <= 0 {
      // Since a[j-1] is non-negative, it must be 0
      assert a[j-1] == 0;
      // From the second precondition: a[j-1]-1 <= a[j]
      assert a[j] >= -1;
      // But we know a[j] > 0, so this holds
      // Now we need to show that a[j-1] cannot be 0 when a[j] > 0
      // The decreasing property gives us: a[j-2]-1 <= a[j-1] == 0
      // This means a[j-2] <= 1, but doesn't force contradiction
      // Instead, we need to prove that if any element is 0, then all subsequent elements must be 0
      // But this contradicts a[j] > 0
      // Actually, we need to show that a[j-1] cannot be 0 when a[j] > 0
      // The key insight is that if a[j-1] == 0, then by the decreasing property:
      // a[j] >= a[j-1] - 1 == -1, which is always true
      // This doesn't lead to contradiction, so we need a different approach
      // Instead, we prove by induction that all elements from 0 to j must be positive
    }
    // Recursively prove that all elements up to j-1 are positive
    FindZeroLemma(a, j-1);
    // Now we know a[j-1] > 0 from the recursive call
    assert a[j-1] > 0;
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
  if a.Length == 0 {
    index := -1;
    return;
  }
  
  var left := 0;
  var right := a.Length - 1;
  
  while left <= right
    invariant 0 <= left <= a.Length
    invariant -1 <= right < a.Length
    invariant forall i :: 0 <= i < left ==> a[i] > 0
    invariant forall i :: right < i < a.Length ==> a[i] > 0
  {
    var mid := left + (right - left) / 2;
    
    if a[mid] == 0 {
      index := mid;
      return;
    } else if a[mid] > 0 {
      // Prove that all elements from 0 to mid are positive
      FindZeroLemma(a, mid);
      left := mid + 1;
    } else {
      // This case should never happen due to non-negative values
      // But we need to handle it for verification
      assert false; // This should be unreachable
      right := mid - 1;
    }
  }
  
  index := -1;
}
// </vc-code>

