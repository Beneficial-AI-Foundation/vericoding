//ATOM

// Predicates for Bubble Sort
predicate sorted(a: array2<int>, l: int, u: int)
  reads a
  requires a.Length1 == 2
{
  forall i, j :: 0 <= l <= i <= j <= u < a.Length0 ==> a[i, 1] <= a[j, 1]
}

//IMPL Bubble Sort

// Bubble Sort
method bubble_sort(a: array2<int>)
  modifies a
  requires a.Length1 == 2
  ensures sorted(a, 0, a.Length0 - 1)
{
  var n := a.Length0;
  
  /* code modified by LLM (iteration 1): Handle edge case when array is empty */
  if n <= 1 {
    return;
  }
  
  var i := 0;
  
  while i < n
    invariant 0 <= i <= n
    /* code modified by LLM (iteration 1): Fixed invariant - last i elements are sorted and >= all previous elements */
    invariant sorted(a, n - i, n - 1)
    invariant forall p, q :: 0 <= p < n - i && n - i <= q < n ==> a[p, 1] <= a[q, 1]
  {
    var j := 0;
    while j < n - 1 - i
      invariant 0 <= j <= n - 1 - i
      /* code modified by LLM (iteration 1): Maintain outer loop invariants in inner loop */
      invariant sorted(a, n - i, n - 1)
      invariant forall p, q :: 0 <= p < n - i && n - i <= q < n ==> a[p, 1] <= a[q, 1]
      /* code modified by LLM (iteration 1): Fixed inner loop invariant - largest element among first n-i elements is bubbled to correct position */
      invariant forall k :: 0 <= k <= j ==> a[k, 1] <= a[n - 1 - i, 1]
    {
      if a[j, 1] > a[j + 1, 1] {
        // Swap rows j and j+1
        var temp0 := a[j, 0];
        var temp1 := a[j, 1];
        a[j, 0] := a[j + 1, 0];
        a[j, 1] := a[j + 1, 1];
        a[j + 1, 0] := temp0;
        a[j + 1, 1] := temp1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}