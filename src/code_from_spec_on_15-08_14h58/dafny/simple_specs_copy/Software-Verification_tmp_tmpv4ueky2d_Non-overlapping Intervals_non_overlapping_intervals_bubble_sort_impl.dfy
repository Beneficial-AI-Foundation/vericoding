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
  var i := 0;
  
  while i < n
    invariant 0 <= i <= n
    /* code modified by LLM (iteration 1): Fixed outer loop invariant - the sorted portion should be from n-i to n-1, not 0 to i-1, since bubble sort moves largest elements to the end */
    invariant sorted(a, n - i, n - 1)
    /* code modified by LLM (iteration 1): Fixed the relationship invariant - elements in the sorted tail (n-i to n-1) should be >= elements in the unsorted part (0 to n-i-1) */
    invariant forall k, l :: 0 <= k < n - i <= l < n ==> a[k, 1] <= a[l, 1]
  {
    var j := 0;
    while j < n - i - 1
      invariant 0 <= j <= n - i - 1
      /* code modified by LLM (iteration 1): Maintained the sorted tail invariant in inner loop */
      invariant sorted(a, n - i, n - 1)
      /* code modified by LLM (iteration 1): Maintained the relationship between unsorted and sorted parts */
      invariant forall k, l :: 0 <= k < n - i <= l < n ==> a[k, 1] <= a[l, 1]
      /* code modified by LLM (iteration 1): Fixed inner loop invariant - the maximum element in range [0..j] should be at position j */
      invariant forall k :: 0 <= k <= j ==> a[k, 1] <= a[j, 1]
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