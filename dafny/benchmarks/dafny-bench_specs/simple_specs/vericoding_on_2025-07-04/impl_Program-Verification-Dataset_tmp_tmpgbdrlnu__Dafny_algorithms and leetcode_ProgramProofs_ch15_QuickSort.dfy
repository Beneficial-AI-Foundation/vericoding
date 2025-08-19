//ATOM

method QuickSortAux(a: array<int>, lo: int, hi: int)
  requires 0 <= lo <= hi <= a.Length
  requires SplitPoint(a, lo) && SplitPoint(a, hi)
  modifies a
  ensures forall i,j :: lo <= i < j < hi ==> a[i] <= a[j]
  ensures SwapFrame(a, lo, hi)
  ensures SplitPoint(a, lo) && SplitPoint(a, hi)
{
  assume forall i,j :: lo <= i < j < hi ==> a[i] <= a[j];
  assume SwapFrame(a, lo, hi);
  assume SplitPoint(a, lo) && SplitPoint(a, hi);
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


//IMPL QuickSort

method QuickSort(a: array<int>)
  modifies a
  ensures forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  ensures multiset(a[..]) == old(multiset(a[..]))
{
  /* code modified by LLM (iteration 1): added base case handling */
  if a.Length <= 1 {
    return;
  }
  
  /* code modified by LLM (iteration 1): establish SplitPoint preconditions using helper lemma */
  EstablishInitialSplitPoints(a);
  
  /* code modified by LLM (iteration 1): store old multiset for preservation proof */
  ghost var oldMultiset := multiset(a[..]);
  
  QuickSortAux(a, 0, a.Length);
  
  /* code modified by LLM (iteration 1): use SwapFrame property to prove multiset preservation */
  SwapFramePreservesMultiset(a, 0, a.Length, oldMultiset);
}

/* code modified by LLM (iteration 1): added helper lemma to establish initial split points */
lemma EstablishInitialSplitPoints(a: array<int>)
  reads a
  ensures SplitPoint(a, 0)
  ensures SplitPoint(a, a.Length)
{
  // SplitPoint(a, 0) is vacuously true since there are no elements with index < 0
  // SplitPoint(a, a.Length) is vacuously true since there are no elements with index >= a.Length
}

/* code modified by LLM (iteration 1): added helper lemma to prove multiset preservation from SwapFrame */
lemma SwapFramePreservesMultiset(a: array<int>, lo: int, hi: int, oldMultiset: multiset<int>)
  requires 0 <= lo <= hi <= a.Length
  requires lo == 0 && hi == a.Length
  requires SwapFrame(a, lo, hi)
  requires oldMultiset == old(multiset(a[..]))
  ensures multiset(a[..]) == oldMultiset
{
  // The SwapFrame property guarantees multiset preservation
}

//IMPL SwapFrame
/* code modified by LLM (iteration 1): defined as twostate predicate to properly handle old() expressions */
twostate predicate SwapFrame(a: array<int>, lo: int, hi: int)
  requires 0 <= lo <= hi <= a.Length
  reads a
{
  multiset(a[lo..hi]) == old(multiset(a[lo..hi])) &&
  forall i :: 0 <= i < lo ==> a[i] == old(a[i]) &&
  forall i :: hi <= i < a.Length ==> a[i] == old(a[i])
}