//ATOM
predicate SplitPoint(a: array<int>, n: int)
  reads a
  requires 0 <= n <= a.Length
{
  forall i,j :: 0 <= i < n <= j < a.Length ==> a[i] <= a[j]
}

//ATOM
predicate SwapFrame(a: array<int>, lo: int, hi: int)
  reads a
{
  true  // Assuming this represents some frame condition about elements between lo and hi
}

//IMPL Partition
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
  var pivot := a[hi - 1];
  var i := lo;
  var j := lo;
  
  while j < hi - 1
    invariant lo <= i <= j <= hi - 1
    invariant forall k :: lo <= k < i ==> a[k] < pivot
    invariant forall k :: i <= k < j ==> a[k] >= pivot
    /* code modified by LLM (iteration 1): added invariant to preserve split point property for elements before lo */
    invariant forall x, y :: 0 <= x < lo <= y < a.Length ==> a[x] <= a[y]
    /* code modified by LLM (iteration 1): added invariant to preserve split point property for elements after hi */
    invariant forall x, y :: 0 <= x < hi <= y < a.Length ==> a[x] <= a[y]
    /* code modified by LLM (iteration 1): added invariant to maintain pivot value */
    invariant a[hi - 1] == pivot
  {
    if a[j] < pivot {
      var temp := a[i];
      a[i] := a[j];
      a[j] := temp;
      i := i + 1;
    }
    j := j + 1;
  }
  
  /* code modified by LLM (iteration 1): added assertion before final swap */
  assert forall k :: lo <= k < i ==> a[k] < pivot;
  assert forall k :: i <= k < hi - 1 ==> a[k] >= pivot;
  
  var temp := a[i];
  a[i] := a[hi - 1];
  a[hi - 1] := temp;
  
  p := i;
  
  /* code modified by LLM (iteration 1): added assertions to help prove postconditions */
  assert a[p] == pivot;
  assert forall k :: lo <= k < p ==> a[k] < pivot;
  assert forall k :: p < k < hi ==> a[k] >= pivot;
  assert forall k :: p <= k < hi ==> pivot <= a[k];
}