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
  /* code modified by LLM (iteration 1): Handle edge case when array is empty or has one element */
  if n <= 1 {
    return;
  }
  
  var i := 0;
  
  while i < n
    invariant 0 <= i <= n
    /* code modified by LLM (iteration 1): Fixed invariant to properly capture that elements from n-i to n-1 are sorted and in final position */
    invariant sorted(a, n - i, n - 1)
    invariant forall k, l :: 0 <= k < n - i && n - i <= l < n ==> a[k, 1] <= a[l, 1]
  {
    var j := 0;
    while j < n - i - 1
      invariant 0 <= j <= n - i - 1
      /* code modified by LLM (iteration 1): Fixed inner loop invariants to maintain sorted suffix and bubbling property */
      invariant sorted(a, n - i, n - 1)
      invariant forall k, l :: 0 <= k < n - i && n - i <= l < n ==> a[k, 1] <= a[l, 1]
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
    /* code modified by LLM (iteration 1): Added assertion to help Dafny verify that the maximum element is now in position n-i-1 */
    assert forall k :: 0 <= k < n - i - 1 ==> a[k, 1] <= a[n - i - 1, 1];
    i := i + 1;
  }
  /* code modified by LLM (iteration 1): Added final assertion to help prove the postcondition */
  assert sorted(a, 0, n - 1);
}