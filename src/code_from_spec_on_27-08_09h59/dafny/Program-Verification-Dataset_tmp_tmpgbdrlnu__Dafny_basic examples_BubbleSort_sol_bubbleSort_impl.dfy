predicate sorted_between (a:array<int>, from:nat, to:nat)
  reads a;
  requires a != null;
  requires from <= to;
  requires to <= a.Length;
{
  forall i,j :: from <= i < j < to && 0 <= i < j < a.Length ==> a[i] <= a[j]
}

predicate sorted (a:array<int>)
  reads a;
  requires a!=null;
{
  sorted_between (a, 0, a.Length)
}

// <vc-helpers>
lemma SortedBetweenExtend(a: array<int>, from: nat, to: nat)
  requires from <= to <= a.Length
  requires sorted_between(a, from, to)
  requires to < a.Length
  requires forall k :: from <= k < to ==> a[k] <= a[to]
  ensures sorted_between(a, from, to + 1)
{
}

lemma SortedBetweenContract(a: array<int>, from: nat, to: nat)
  requires from < to <= a.Length
  requires sorted_between(a, from, to)
  ensures sorted_between(a, from, to - 1)
{
}

lemma SortedAfterSwap(a: array<int>, i: nat, j: nat)
  requires i < j < a.Length
  requires a[i] > a[j]
  requires sorted_between(a, 0, i + 1)
  requires sorted_between(a, j, a.Length)
  requires forall k :: 0 <= k < i ==> a[k] <= a[j]
  requires forall k :: j < k < a.Length ==> a[i] <= a[k]
  ensures sorted_between(a, 0, i + 1)
  ensures sorted_between(a, j, a.Length)
  ensures multiset(old(a[..])) == multiset(a[..])
{
}

lemma BubbleInnerLoopLemma(a: array<int>, n: int, i: int, j: int)
  requires 0 <= i < n - 1
  requires 0 <= j <= n - 1 - i
  requires n == a.Length
  requires sorted_between(a, n - i, n)
  requires forall k :: j <= k < n - 1 - i ==> a[k] <= a[n - 1 - i]
  ensures forall k :: j <= k < n - 1 - i ==> a[k] <= a[n - 1 - i]
{
}

lemma MaxElementLemma(a: array<int>, start: int, end: int)
  requires 0 <= start < end <= a.Length
  requires forall k :: start <= k < end - 1 ==> a[k] <= a[end - 1]
  ensures forall k :: start <= k < end ==> a[k] <= a[end - 1]
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method bubbleSort (a: array<int>)
  modifies a;
  requires a != null;
  requires a.Length > 0;
  ensures sorted(a);
  ensures multiset(old(a[..])) == multiset(a[..]);
// </vc-spec>
// </vc-spec>

// <vc-code>
{
  var n := a.Length;
  var i := 0;
  
  while i < n - 1
    invariant 0 <= i <= n - 1
    invariant sorted_between(a, n - i, n)
    invariant multiset(old(a[..])) == multiset(a[..])
    invariant forall k1, k2 :: n - i <= k1 < k2 < n ==> a[k1] <= a[k2]
    invariant forall k1, k2 :: 0 <= k1 < n - i && n - i <= k2 < n ==> a[k1] <= a[k2]
  {
    var j := 0;
    
    while j < n - 1 - i
      invariant 0 <= j <= n - 1 - i
      invariant sorted_between(a, n - i, n)
      invariant multiset(old(a[..])) == multiset(a[..])
      invariant forall k1, k2 :: 0 <= k1 < n - i && n - i <= k2 < n ==> a[k1] <= a[k2]
      invariant forall k :: 0 <= k < j ==> a[k] <= a[j]
      invariant j < n - 1 - i ==> forall k :: j + 1 <= k < n - 1 - i ==> a[j] <= a[k]
    {
      if a[j] > a[j + 1] {
        a[j], a[j + 1] := a[j + 1], a[j];
      }
      j := j + 1;
    }
    
    MaxElementLemma(a, 0, n - i);
    i := i + 1;
  }
}
// </vc-code>
