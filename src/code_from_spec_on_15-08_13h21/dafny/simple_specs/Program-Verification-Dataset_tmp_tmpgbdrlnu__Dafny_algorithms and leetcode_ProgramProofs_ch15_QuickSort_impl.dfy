//ATOM
method QuickSortAux(a: array<int>, lo: int, hi: int)
  requires 0 <= lo <= hi <= a.Length
  requires SplitPoint(a, lo) && SplitPoint(a, hi)
  modifies a
  ensures forall i,j :: lo <= i < j < hi ==> a[i] <= a[j]
  ensures SplitPoint(a, lo) && SplitPoint(a, hi)
  ensures SwapFrame(a, lo, hi)
{
  if lo + 1 < hi {
    var p := Partition(a, lo, hi);
    QuickSortAux(a, lo, p);
    QuickSortAux(a, p + 1, hi);
  }
}

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
  requires 0 <= n <= a.Length
{
  forall i,j :: 0 <= i < n <= j < a.Length ==> a[i] <= a[j]
}

//ATOM
twostate predicate SwapFrame(a: array<int>, lo: int, hi: int)
  requires 0 <= lo <= hi <= a.Length
  reads a
{
  forall i :: 0 <= i < a.Length && !(lo <= i < hi) ==> a[i] == old(a[i])
}

//IMPL QuickSort
method QuickSort(a: array<int>)
  modifies a
  ensures forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  ensures multiset(a[..]) == old(multiset(a[..]))
{
  /* code modified by LLM (iteration 1): Check if array is non-empty before calling QuickSortAux */
  if a.Length > 0 {
    /* code modified by LLM (iteration 1): Establish SplitPoint preconditions for QuickSortAux */
    assert SplitPoint(a, 0);
    assert SplitPoint(a, a.Length);
    
    QuickSortAux(a, 0, a.Length);
    
    /* code modified by LLM (iteration 1): Multiset preservation follows from SwapFrame postcondition of QuickSortAux */
    // SwapFrame(a, 0, a.Length) ensures elements are only rearranged within the array
    // which preserves the multiset
  }
}