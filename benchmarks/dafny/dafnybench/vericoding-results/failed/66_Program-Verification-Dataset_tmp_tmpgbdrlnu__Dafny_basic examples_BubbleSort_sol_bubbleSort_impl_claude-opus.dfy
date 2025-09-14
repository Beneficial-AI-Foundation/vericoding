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
lemma SortedBetweenTransitive(a: array<int>, from: nat, mid: nat, to: nat)
  requires a != null
  requires from <= mid <= to <= a.Length
  requires sorted_between(a, from, mid)
  requires sorted_between(a, mid, to)
  requires mid > from && mid < to ==> a[mid-1] <= a[mid]
  ensures sorted_between(a, from, to)
{
}

lemma SortedBetweenExtend(a: array<int>, from: nat, to: nat)
  requires a != null
  requires from < to <= a.Length
  requires sorted_between(a, from, to-1)
  requires forall k :: from <= k < to-1 ==> a[k] <= a[to-1]
  ensures sorted_between(a, from, to)
{
}

lemma SwapPreservesMultiset(a: array<int>, i: nat, j: nat, old_a: seq<int>)
  requires a != null
  requires i < a.Length && j < a.Length
  requires i != j
  requires a[..] == old_a[i := old_a[j]][j := old_a[i]]
  ensures multiset(a[..]) == multiset(old_a)
{
  var a' := a[..];
  assert a'[i] == old_a[j] && a'[j] == old_a[i];
  assert forall k :: 0 <= k < a.Length && k != i && k != j ==> a'[k] == old_a[k];
}

lemma BubbleStepMaintainsSorted(a: array<int>, i: nat, j: nat)
  requires a != null
  requires 0 <= j < i < a.Length
  requires sorted_between(a, i, a.Length)
  requires forall k, l :: 0 <= k <= i < l < a.Length ==> a[k] <= a[l]
  requires forall k :: 0 <= k <= j ==> a[k] <= a[j+1]
  ensures sorted_between(a, i, a.Length)
{
}
// </vc-helpers>

// <vc-spec>
method bubbleSort (a: array<int>)
  modifies a;
  requires a != null;
  requires a.Length > 0;
  ensures sorted(a);
  ensures multiset(old(a[..])) == multiset(a[..]);
// </vc-spec>
// <vc-code>
{
  var n := a.Length;
  var i := n - 1;
  
  while i > 0
    invariant 0 <= i < n
    invariant sorted_between(a, i, n)
    invariant forall k, l :: 0 <= k <= i < l < n ==> a[k] <= a[l]
    invariant multiset(a[..]) == multiset(old(a[..]))
  {
    var j := 0;
    while j < i
      invariant 0 <= j <= i
      invariant sorted_between(a, i, n)
      invariant forall k :: 0 <= k < j ==> a[k] <= a[j]
      invariant forall k, l :: 0 <= k <= i < l < n ==> a[k] <= a[l]
      invariant multiset(a[..]) == multiset(old(a[..]))
    {
      if a[j] > a[j+1] {
        ghost var old_seq := a[..];
        var temp := a[j];
        a[j] := a[j+1];
        a[j+1] := temp;
        SwapPreservesMultiset(a, j, j+1, old_seq);
      }
      j := j + 1;
    }
    i := i - 1;
  }
}
// </vc-code>

