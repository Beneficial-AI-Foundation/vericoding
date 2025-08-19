//ATOM

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


//IMPL 

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
    /* code modified by LLM (iteration 1): Fixed outer loop invariant to properly capture that elements from n-i onwards are in their final sorted positions */
    invariant sorted_between(A, n - i, n - 1)
    /* code modified by LLM (iteration 1): Added invariant to ensure elements in the sorted suffix are greater than or equal to elements in the unsorted prefix */
    invariant forall k, l :: 0 <= k < n - i && n - i <= l < n ==> A[k] <= A[l]
  {
    var j := 0;
    
    while j < n - 1 - i
      invariant 0 <= j <= n - 1 - i
      invariant multiset(A[..]) == multiset(old(A[..]))
      invariant sorted_between(A, n - i, n - 1)
      invariant forall k, l :: 0 <= k < n - i && n - i <= l < n ==> A[k] <= A[l]
      /* code modified by LLM (iteration 1): Fixed inner loop invariant to correctly state that the maximum element in range [0, j] has bubbled to position j */
      invariant forall k :: 0 <= k <= j ==> A[k] <= A[j]
    {
      if A[j] > A[j + 1] {
        A[j], A[j + 1] := A[j + 1], A[j];
      }
      j := j + 1;
    }
    i := i + 1;
  }
  
  /* code modified by LLM (iteration 1): Added assertion to help Dafny verify that the entire array is sorted */
  assert sorted_between(A, 0, n - 1);
}