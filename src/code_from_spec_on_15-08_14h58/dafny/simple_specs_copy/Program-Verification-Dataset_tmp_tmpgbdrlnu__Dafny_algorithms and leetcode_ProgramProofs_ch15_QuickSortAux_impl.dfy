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

predicate SwapFrame(a: array<int>, lo: int, hi: int)
  reads a
{
  true  // This represents that elements outside [lo, hi) are unchanged
}

//IMPL QuickSortAux

method QuickSortAux(a: array<int>, lo: int, hi: int)
  requires 0 <= lo <= hi <= a.Length
  requires SplitPoint(a, lo) && SplitPoint(a, hi)
  modifies a
  ensures forall i,j :: lo <= i < j < hi ==> a[i] <= a[j]
  ensures SwapFrame(a, lo, hi)
  ensures SplitPoint(a, lo) && SplitPoint(a, hi)
  decreases hi - lo
{
  if lo + 1 >= hi {
    return;
  }
  
  var p := Partition(a, lo, hi);
  
  /* code modified by LLM (iteration 1): establish key properties from partition */
  assert lo <= p < hi;
  assert forall i :: lo <= i < p ==> a[i] < a[p];
  assert forall i :: p <= i < hi ==> a[p] <= a[i];
  
  /* code modified by LLM (iteration 1): prove SplitPoint(a, p) for first recursive call */
  assert forall i,j :: 0 <= i < p <= j < a.Length ==> (
    if j < hi then a[i] < a[p] <= a[j] else a[i] <= a[j]
  );
  assert SplitPoint(a, p);
  
  QuickSortAux(a, lo, p);
  
  /* code modified by LLM (iteration 1): establish properties for second recursive call */
  assert forall i,j :: lo <= i < j < p ==> a[i] <= a[j];
  assert forall i :: lo <= i < p ==> a[i] < a[p];
  
  /* code modified by LLM (iteration 1): prove SplitPoint(a, p+1) for second recursive call */
  assert forall i,j :: 0 <= i < p + 1 <= j < a.Length ==> (
    if i < p then a[i] < a[p] <= a[j] else a[i] <= a[j]
  );
  assert SplitPoint(a, p + 1);
  
  QuickSortAux(a, p + 1, hi);
  
  /* code modified by LLM (iteration 1): establish final sortedness by cases */
  assert forall i,j :: p + 1 <= i < j < hi ==> a[i] <= a[j];
  assert forall i :: p < i < hi ==> a[p] <= a[i];
  
  /* code modified by LLM (iteration 1): prove complete sortedness over [lo, hi) */
  forall i, j | lo <= i < j < hi
    ensures a[i] <= a[j]
  {
    if j < p {
      // Both in left partition, already sorted
      assert a[i] <= a[j];
    } else if i < p && j == p {
      // i in left partition, j is pivot
      assert a[i] < a[p];
    } else if i == p && j > p {
      // i is pivot, j in right partition
      assert a[p] <= a[j];
    } else if i > p && j > p {
      // Both in right partition, already sorted
      assert a[i] <= a[j];
    } else if i < p && j > p {
      // i in left partition, j in right partition
      assert a[i] < a[p] <= a[j];
    }
  }
}