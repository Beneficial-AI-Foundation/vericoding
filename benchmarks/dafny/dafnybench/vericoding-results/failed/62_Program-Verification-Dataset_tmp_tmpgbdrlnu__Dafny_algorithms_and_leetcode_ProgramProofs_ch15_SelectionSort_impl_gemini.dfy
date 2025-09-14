// <vc-preamble>
predicate SplitPoint(a: array<int>, n: int)
    reads a
    requires 0 <= n <= n

{
    forall i,j :: 0 <= i < n <= j < a.Length ==> a[i] <= a[j]
}

twostate predicate SwapFrame(a: array<int>, lo: int, hi: int)
    requires 0 <= lo <= hi <= a.Length
    reads a
{
    (forall i :: 0 <= i < lo || hi <= i < a.Length ==> a[i] == old(a[i])) && multiset(a[..]) == old(multiset(a[..]))
}
// </vc-preamble>

// <vc-helpers>
predicate SortedPrefix(a: array<int>, n: int)
  reads a
  requires 0 <= n <= a.Length
{
  forall i, j :: 0 <= i < j < n ==> a[i] <= a[j]
}
// </vc-helpers>

// <vc-spec>
method SelectionSort(a: array<int>)
    modifies a
    ensures forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
    ensures multiset(a[..]) == old(multiset(a[..]))
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant multiset(old(a)[..]) == multiset(a[..])
    invariant SortedPrefix(a, i)
    invariant SplitPoint(a, i)
  {
    var min_idx := i;
    var j := i + 1;
    while j < a.Length
      invariant i < j <= a.Length
      invariant i <= min_idx < j
      invariant forall k :: i <= k < j ==> a[min_idx] <= a[k]
    {
      if a[j] < a[min_idx] {
        min_idx := j;
      }
      j := j + 1;
    }

    a[i], a[min_idx] := a[min_idx], a[i];

    i := i + 1;
  }
}
// </vc-code>
