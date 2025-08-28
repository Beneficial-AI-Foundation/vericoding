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

// <vc-helpers>
lemma SwapPreservesMultiset(a: array<int>, i: int, j: int)
  requires 0 <= i < a.Length && 0 <= j < a.Length
  ensures multiset(a[..]) == multiset(old(a[..]))
{
}

lemma SwapPreservesSplitPoint(a: array<int>, lo: int, hi: int, i: int, j: int)
  requires 0 <= lo <= hi <= a.Length
  requires SplitPoint(a, lo) && SplitPoint(a, hi)
  requires 0 <= i < a.Length && 0 <= j < a.Length
  ensures SplitPoint(a, lo) && SplitPoint(a, hi)
{
}
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>

// <vc-code>
method PartitionImpl(a: array<int>, lo: int, hi: int) returns (p: int)
  requires 0 <= lo < hi <= a.Length
  requires SplitPoint(a, lo) && SplitPoint(a, hi)
  modifies a
  ensures lo <= p < hi
  ensures forall i :: lo <= i < p ==> a[i] < a[p]
  ensures forall i :: p <= i < hi ==> a[p] <= a[i]
  ensures SplitPoint(a, lo) && SplitPoint(a, hi)
  ensures SwapFrame(a, lo, hi)
{
  var pivot := a[hi - 1];
  var i := lo;
  var j := lo;
  
  while j < hi - 1
    invariant lo <= i <= j <= hi - 1
    invariant forall k :: lo <= k < i ==> a[k] < pivot
    invariant forall k :: i <= k < j ==> a[k] >= pivot
    invariant SplitPoint(a, lo) && SplitPoint(a, hi)
    invariant multiset(a[..]) == old(multiset(a[..]))
    invariant forall k :: 0 <= k < lo || hi <= k < a.Length ==> a[k] == old(a[k])
  {
    if a[j] < pivot {
      var temp := a[i];
      a[i] := a[j];
      a[j] := temp;
      SwapPreservesMultiset(a, i, j);
      SwapPreservesSplitPoint(a, lo, hi, i, j);
      i := i + 1;
    }
    j := j + 1;
  }
  
  var temp := a[i];
  a[i] := a[hi - 1];
  a[hi - 1] := temp;
  SwapPreservesMultiset(a, i, hi - 1);
  SwapPreservesSplitPoint(a, lo, hi, i, hi - 1);
  
  p := i;
  // Additional assertions to help verification
  assert a[p] == a[i];
  assert forall k :: lo <= k < p ==> a[k] < a[p];
  assert forall k :: p < k < hi ==> a[k] >= a[p];
}
// </vc-code>
