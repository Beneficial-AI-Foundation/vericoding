predicate sorted(A:array<int>)
  reads A
{
  sorted_between(A, 0, A.Length-1)
}


//ATOM

predicate sorted_between(A:array<int>, from:int, to:int)
  reads A
{
  forall i, j :: 0 <= i <= j < A.Length && from <= i <= j <= to ==> A[i] <= A[j]
}


//IMPL BubbleSort

method BubbleSort(A:array<int>)
  modifies A
  ensures sorted(A)
  ensures multiset(A[..]) == multiset(old(A[..]))
{
  if A.Length <= 1 {
    return;
  }
  
  var n := A.Length;
  var i := 0;
  
  while i < n - 1
    invariant 0 <= i <= n - 1
    invariant multiset(A[..]) == multiset(old(A[..]))
    /* code modified by LLM (iteration 1): replaced incorrect invariant with proper bubble sort invariant */
    invariant sorted_between(A, n - i, n - 1)
    /* code modified by LLM (iteration 1): added invariant to capture that elements in sorted suffix are >= elements before it */
    invariant forall k, l :: 0 <= k < n - i && n - i <= l < n ==> A[k] <= A[l]
  {
    var j := 0;
    
    while j < n - 1 - i
      invariant 0 <= j <= n - 1 - i
      invariant multiset(A[..]) == multiset(old(A[..]))
      /* code modified by LLM (iteration 1): updated inner loop invariants to match outer loop */
      invariant sorted_between(A, n - i, n - 1)
      invariant forall k, l :: 0 <= k < n - i && n - i <= l < n ==> A[k] <= A[l]
      /* code modified by LLM (iteration 1): added invariant to track that largest element is bubbled to position j */
      invariant forall k :: 0 <= k <= j ==> A[k] <= A[j]
    {
      if A[j] > A[j + 1] {
        var temp := A[j];
        A[j] := A[j + 1];
        A[j + 1] := temp;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}