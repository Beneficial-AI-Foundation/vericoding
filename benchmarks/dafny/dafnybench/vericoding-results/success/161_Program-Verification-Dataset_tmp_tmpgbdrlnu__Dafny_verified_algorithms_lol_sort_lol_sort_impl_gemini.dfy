// <vc-preamble>
predicate valid_permut(a: seq<int>, b: seq<int>)
  requires |a| == |b|
{
  multiset(a) == multiset(b)
}

method swap(a: array<int>, i: int, j: int)
  requires 0 <= i < a.Length && 0 <= j < a.Length
  modifies a
  ensures a[..] == old(a[..]) [i := old(a[j])] [j := old(a[i])]
  ensures valid_permut(a[..], old(a[..]))
{
  assume{:axiom} false;
}

predicate sorted(a: seq<int>)
{
  forall i, j | 0 <= i <= j < |a| :: a[i] <= a[j]
}
// </vc-preamble>

// <vc-helpers>
method findMinIndex(a: array<int>, start: int) returns (minIndex: int)
  requires 0 <= start < a.Length
  ensures start <= minIndex < a.Length
  ensures forall k :: start <= k < a.Length ==> a[minIndex] <= a[k]
{
  minIndex := start;
  var j := start + 1;
  while j < a.Length
    invariant start <= j <= a.Length
    invariant start <= minIndex < j
    invariant forall k :: start <= k < j ==> a[minIndex] <= a[k]
  {
    if a[j] < a[minIndex] {
      minIndex := j;
    }
    j := j + 1;
  }
}
// </vc-helpers>

// <vc-spec>
method lol_sort(a: array<int>)
  modifies a
  ensures valid_permut(a[..], old(a[..]))
  ensures sorted(a[..])
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant valid_permut(a[..], old(a[..]))
    invariant sorted(a[..i])
    invariant forall k1, k2 :: 0 <= k1 < i <= k2 < a.Length ==> a[k1] <= a[k2]
  {
    var min_idx := findMinIndex(a, i);
    swap(a, i, min_idx);
    i := i + 1;
  }
}
// </vc-code>
