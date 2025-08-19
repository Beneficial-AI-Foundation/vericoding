method FIND(A: array<int>, N: int, f: int)
 requires A.Length == N
 requires 0 <= f < N
 modifies A
 ensures forall p,q :: 0 <= p <= f <= q < N ==> A[p] <= A[q]
{
  /* code modified by LLM (iteration 4): use selection sort to properly maintain sorted invariant */
  var i := 0;
  while i < N - 1
    invariant 0 <= i <= N - 1
    /* code modified by LLM (iteration 4): corrected invariant to match selection sort behavior */
    invariant forall p, q :: 0 <= p < q < i ==> A[p] <= A[q]
    invariant forall p, q :: 0 <= p < i && i <= q < N ==> A[p] <= A[q]
  {
    /* code modified by LLM (iteration 4): find minimum element in remaining array */
    var minIdx := i;
    var j := i + 1;
    while j < N
      invariant i + 1 <= j <= N
      invariant i <= minIdx < j
      invariant forall k :: i <= k < j ==> A[minIdx] <= A[k]
    {
      if A[j] < A[minIdx] {
        minIdx := j;
      }
      j := j + 1;
    }
    
    /* code modified by LLM (iteration 4): swap minimum to position i */
    if minIdx != i {
      A[i], A[minIdx] := A[minIdx], A[i];
    }
    i := i + 1;
  }
}

method FIND_Helper(A: array<int>, start: int, end: int, f: int)
  requires A.Length >= end > start >= 0
  requires start <= f < end
  modifies A
  ensures forall p,q :: start <= p <= f <= q < end ==> A[p] <= A[q]
  decreases end - start
{
  if start >= end - 1 {
    return;
  }
  
  /* code modified by LLM (iteration 4): use selection sort with corrected invariants */
  var i := start;
  while i < end - 1
    invariant start <= i <= end - 1
    /* code modified by LLM (iteration 4): corrected invariant to match selection sort behavior */
    invariant forall p, q :: start <= p < q < i ==> A[p] <= A[q]
    invariant forall p, q :: start <= p < i && i <= q < end ==> A[p] <= A[q]
  {
    /* code modified by LLM (iteration 4): find minimum in remaining range */
    var minIdx := i;
    var j := i + 1;
    while j < end
      invariant i + 1 <= j <= end
      invariant i <= minIdx < j
      invariant forall k :: i <= k < j ==> A[minIdx] <= A[k]
    {
      if A[j] < A[minIdx] {
        minIdx := j;
      }
      j := j + 1;
    }
    
    /* code modified by LLM (iteration 4): swap minimum to position i */
    if minIdx != i {
      A[i], A[minIdx] := A[minIdx], A[i];
    }
    i := i + 1;
  }
}