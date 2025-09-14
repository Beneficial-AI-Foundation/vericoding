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

// </vc-helpers>

// <vc-spec>
method Partition(a: array<int>, lo: int, hi: int) returns (p: int)
    requires 0 <= lo < hi <= a.Length
    requires SplitPoint(a, lo) && SplitPoint(a, hi)
    modifies a
    ensures lo <= p < hi
    ensures forall i :: lo <= i < p ==> a[i] < a[p]
    ensures forall i :: p <= i < hi ==> a[p] <= a[i]
    ensures SplitPoint(a, lo) && SplitPoint(a, hi)
    ensures SwapFrame(a, lo, hi)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): use whole-array multiset invariant */
  var pivot := a[hi - 1];
  p := lo;
  var j := lo;
  while j < hi - 1
    invariant 0 <= lo <= p <= j <= hi - 1
    invariant a[hi - 1] == pivot
    invariant forall k :: lo <= k < p ==> a[k] < pivot
    invariant forall k :: p <= k < j ==> a[k] >= pivot
    invariant multiset(a[..]) == old(multiset(a[..]))
    invariant forall k :: 0 <= k < lo || hi <= k < a.Length ==> a[k] == old(a[k])
    invariant SplitPoint(a, lo)
    invariant SplitPoint(a, hi)
  {
    if a[j] < pivot {
      a[p], a[j] := a[j], a[p];
      p := p + 1;
    }
    j := j + 1;
  }
  a[p], a[hi-1] := a[hi-1], a[p];
}
// </vc-code>
