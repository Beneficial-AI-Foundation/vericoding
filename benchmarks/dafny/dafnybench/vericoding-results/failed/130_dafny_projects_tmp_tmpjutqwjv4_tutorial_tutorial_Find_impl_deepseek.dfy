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
lemma binary_search_lemma(a: array<int>, low: int, high: int, key: int)
  requires 0 <= low <= high <= a.Length
  requires sorted(a)
  requires forall i : int :: 0 <= i < a.Length ==> a[i] != key
  ensures forall k :: 0 <= k < a.Length ==> a[k] != key
{
}

lemma binary_search_found(a: array<int>, i: int, key: int)
  requires 0 <= i < a.Length
  requires sorted(a)
  requires a[i] == key
  ensures exists k :: 0 <= k < a.Length && a[k] == key
{
}

lemma binary_search_range(a: array<int>, low: int, high: int, mid: int, key: int)
  requires 0 <= low <= mid < high <= a.Length
  requires sorted(a)
  requires a[mid] < key
  ensures forall k :: low <= k <= mid ==> a[k] < key
{
  forall k | low <= k <= mid
    ensures a[k] < key
  {
    if k < mid {
      assert a[k] <= a[mid] < key;
    } else if k == mid {
      assert a[k] < key;
    }
  }
}

lemma binary_search_range2(a: array<int>, low: int, high: int, mid: int, key: int)
  requires 0 <= low <= mid < high <= a.Length
  requires sorted(a)
  requires a[mid] > key
  ensures forall k :: mid <= k < high ==> a[k] > key
{
  forall k | mid <= k < high
    ensures a[k] > key
  {
    if k > mid {
      assert key < a[mid] <= a[k];
    } else if k == mid {
      assert a[k] > key;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method Find(a: array<int>, key: int) returns (index: int)
  ensures 0 <= index ==> index < a.Length && a[index] == key
  ensures index < 0 ==> (forall k :: 0 <= k < a.Length ==> a[k] != key)
// </vc-spec>
// <vc-code>
{
  var low := 0;
  var high := a.Length;
  index := -1;
  
  while low < high
    invariant 0 <= low <= high <= a.Length
    invariant index == -1 ==> forall k :: 0 <= k < low ==> a[k] != key
    invariant index == -1 ==> forall k :: high <= k < a.Length ==> a[k] != key
    decreases high - low
  {
    var mid := (low + high) / 2;
    
    if a[mid] == key {
      index := mid;
      return;
    } else if a[mid] < key {
      binary_search_range(a, low, high, mid, key);
      low := mid + 1;
    } else {
      binary_search_range2(a, low, high, mid, key);
      high := mid;
    }
  }
}
// </vc-code>

