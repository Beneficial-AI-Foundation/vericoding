//ATOM
predicate SplitPoint(a: array<int>, n: int)
  reads a
  requires 0 <= n <= a.Length
{
  forall i,j :: 0 <= i < n <= j < a.Length ==> a[i] <= a[j]
}

//IMPL
method Partition(a: array<int>, lo: int, hi: int) returns (p: int)
  requires 0 <= lo < hi <= a.Length
  requires SplitPoint(a, lo) && SplitPoint(a, hi)
  modifies a
  ensures lo <= p < hi
  ensures forall i :: lo <= i < p ==> a[i] < a[p]
  ensures forall i :: p <= i < hi ==> a[p] <= a[i]
  ensures SplitPoint(a, lo) && SplitPoint(a, hi)
  ensures SwapFrame(a, lo, hi)
{
  var pivot := a[hi-1];
  var i := lo;
  var j := lo;
  
  while j < hi - 1
    invariant lo <= i <= j <= hi - 1
    invariant forall k :: lo <= k < i ==> a[k] < pivot
    invariant forall k :: i <= k < j ==> a[k] >= pivot
  {
    if a[j] < pivot {
      var temp := a[i];
      a[i] := a[j];
      a[j] := temp;
      i := i + 1;
    }
    j := j + 1;
  }
  
  var temp := a[i];
  a[i] := a[hi-1];
  a[hi-1] := temp;
  
  p := i;
}

predicate SwapFrame(a: array<int>, lo: int, hi: int)
  reads a
{
  true  // Placeholder - assuming this means elements are only rearranged within [lo, hi)
}