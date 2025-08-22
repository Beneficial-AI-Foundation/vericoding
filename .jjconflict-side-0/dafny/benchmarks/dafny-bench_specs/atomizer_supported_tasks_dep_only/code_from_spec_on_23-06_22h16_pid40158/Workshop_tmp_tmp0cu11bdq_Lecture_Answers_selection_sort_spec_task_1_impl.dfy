//ATOM 

predicate sorted' (a: array<int>, i: int)
	requires a != null
	requires 0 <= i <= a.Length
	reads a
{
	forall k :: 0 < k < i ==> a[k-1] <= a[k]
}

//IMPL Selection sort on arrays

method SelectionSort(a: array<int>) 
  modifies a
  ensures sorted'(a, a.Length)
{
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant sorted'(a, i)
    invariant forall j, k :: 0 <= j < i <= k < a.Length ==> a[j] <= a[k]
  {
    var minIndex := i;
    var j := i + 1;
    
    /* code modified by LLM (iteration 1): Added invariant to ensure minIndex stays within valid bounds and maintains minimum property */
    while j < a.Length
      invariant i <= minIndex < a.Length
      invariant i + 1 <= j <= a.Length
      invariant forall k :: i <= k < j ==> a[minIndex] <= a[k]
      invariant minIndex >= i
    {
      if a[j] < a[minIndex] {
        minIndex := j;
      }
      j := j + 1;
    }
    
    /* code modified by LLM (iteration 1): Added assertion to help verification understand the minimum property holds for the entire remaining array */
    assert forall k :: i <= k < a.Length ==> a[minIndex] <= a[k];
    
    if minIndex != i {
      var temp := a[i];
      a[i] := a[minIndex];
      a[minIndex] := temp;
    }
    
    /* code modified by LLM (iteration 1): Added assertion to help verify that after swap, the sorted portion is maintained and the partitioning property holds */
    assert forall j, k :: 0 <= j < i + 1 <= k < a.Length ==> a[j] <= a[k];
    
    i := i + 1;
  }
}