method BubbleSort(A:array<int>)
  modifies A
  ensures sorted(A)
  ensures multiset(A[..]) == multiset(old(A[..]))
{
  /* code modified by LLM (iteration 4): Fixed invariants to properly model bubble sort - removed problematic partitioning invariant, fixed index bounds, and corrected inner loop logic */
  var n := A.Length;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant multiset(A[..]) == multiset(old(A[..]))
    invariant sorted_between(A, n-i, n-1)
    /* code modified by LLM (iteration 4): Added invariant that elements in sorted suffix are >= elements before it */
    invariant forall x, y :: 0 <= x < n-i && n-i <= y < n ==> A[x] <= A[y]
  {
    var j := 0;
    /* code modified by LLM (iteration 4): Fixed inner loop bounds and invariants to avoid index out of range */
    while j < n - i - 1
      invariant 0 <= j <= n - i - 1
      invariant multiset(A[..]) == multiset(old(A[..]))
      invariant sorted_between(A, n-i, n-1)
      /* code modified by LLM (iteration 4): Preserved outer loop's partitioning property during inner loop */
      invariant forall x, y :: 0 <= x < n-i && n-i <= y < n ==> A[x] <= A[y]
      /* code modified by LLM (iteration 4): Fixed bubbling invariant - maximum element up to j is at position j */
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

//IMPL Main
method Main() {
  var A := new int[10];
  A[0], A[1], A[2], A[3], A[4], A[5], A[6], A[7], A[8], A[9] := 2, 4, 6, 15, 3, 19, 17, 16, 18, 1;
  BubbleSort(A);
  print A[..];
}