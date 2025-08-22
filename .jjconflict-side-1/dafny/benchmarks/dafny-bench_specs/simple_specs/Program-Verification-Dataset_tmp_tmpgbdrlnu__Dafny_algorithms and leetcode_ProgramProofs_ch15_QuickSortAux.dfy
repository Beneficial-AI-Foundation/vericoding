//ATOM

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
  p := 0;
  assume lo <= p < hi;
  assume forall i :: lo <= i < p ==> a[i] < a[p];
  assume forall i :: p <= i < hi ==> a[p] <= a[i];
  assume SplitPoint(a, lo) && SplitPoint(a, hi);
  assume SwapFrame(a, lo, hi);
  return p;
}


//ATOM
predicate SplitPoint(a: array<int>, n: int)
  reads a
  requires 0 <= n <= n

{
  forall i,j :: 0 <= i < n <= j < a.Length ==> a[i] <= a[j]
}


// SPEC

method QuickSortAux(a: array<int>, lo: int, hi: int)
  requires 0 <= lo <= hi <= a.Length
  requires SplitPoint(a, lo) && SplitPoint(a, hi)
  modifies a
  ensures forall i,j :: lo <= i < j < hi ==> a[i] <= a[j]
  ensures SwapFrame(a, lo, hi)
  ensures SplitPoint(a, lo) && SplitPoint(a, hi)
{
}
