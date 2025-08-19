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
    /* code modified by LLM (iteration 1): Fixed invariant - elements from n-i to n-1 are sorted and in final position */
    invariant sorted_between(A, n - i, n - 1)
    /* code modified by LLM (iteration 1): Elements in unsorted part are <= elements in sorted part */
    invariant forall k, l :: 0 <= k < n - i && n - i <= l < n ==> A[k] <= A[l]
  {
    var j := 0;
    
    while j < n - 1 - i
      invariant 0 <= j <= n - 1 - i
      invariant multiset(A[..]) == multiset(old(A[..]))
      invariant sorted_between(A, n - i, n - 1)
      invariant forall k, l :: 0 <= k < n - i && n - i <= l < n ==> A[k] <= A[l]
      /* code modified by LLM (iteration 1): After j iterations, max element in range 0..j is at position j */
      invariant forall k :: 0 <= k <= j ==> A[k] <= A[j]
    {
      if A[j] > A[j + 1] {
        A[j], A[j + 1] := A[j + 1], A[j];
      }
      j := j + 1;
    }
    
    i := i + 1;
  }
}