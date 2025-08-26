// Bubble Sort

// <vc-helpers>
// Helper lemmas for bubble sort verification
lemma PartitionedExtend(a: array2<int>, i: int)
    requires a.Length1 == 2
    requires 0 <= i < a.Length0 - 1
    requires partitioned(a, i - 1)
    requires sorted(a, i + 1, a.Length0 - 1)
    requires forall k :: 0 <= k <= i ==> a[k, 1] <= a[i + 1, 1]
    ensures partitioned(a, i)
{
}

lemma SortedPreserved(a: array2<int>, i: int, j: int)
    requires a.Length1 == 2
    requires 0 <= i < a.Length0
    requires i <= j < a.Length0 - i
    requires sorted(a, i, a.Length0 - 1)
    ensures sorted(a, i, a.Length0 - 1)
{
}

lemma BubbleCorrectness(a: array2<int>, i: int)
    requires a.Length1 == 2
    requires 0 <= i <= a.Length0 - 1
    requires partitioned(a, i - 1)
    requires sorted(a, i, a.Length0 - 1)
    ensures sorted(a, 0, a.Length0 - 1)
{
    if i == 0 {
        return;
    }
    
    // Since we have partitioned(a, i-1) and sorted(a, i, a.Length0-1),
    // and all elements in [0..i-1] are <= all elements in [i..a.Length0-1],
    // the entire array is sorted
    assert forall k, k' :: 0 <= k <= i-1 < k' < a.Length0 ==> a[k, 1] <= a[k', 1];
    assert forall k, k' :: i <= k <= k' < a.Length0 ==> a[k, 1] <= a[k', 1];
}

lemma SortedMaintainedAfterSwap(a: array2<int>, j: int, i: int)
    requires a.Length1 == 2
    requires 0 <= j < a.Length0 - 1
    requires 0 <= i < a.Length0 - 1
    requires j < a.Length0 - 1 - i
    requires sorted(a, i + j + 2, a.Length0 - 1)
    requires a[j, 1] > a[j + 1, 1]
    ensures sorted(a, i + j + 2, a.Length0 - 1)
{
}
// </vc-helpers>

// <vc-spec>
method bubble_sort(a: array2<int>)
    modifies a
    requires a.Length1 == 2
    ensures sorted(a, 0, a.Length0 - 1)
// </vc-spec>
// <vc-code>
{
  if a.Length0 <= 1 {
    return;
  }
  
  var i := 0;
  while i < a.Length0 - 1
    invariant 0 <= i <= a.Length0 - 1
    invariant partitioned(a, i - 1)
    invariant sorted(a, i, a.Length0 - 1)
  {
    var j := 0;
    while j < a.Length0 - 1 - i
      invariant 0 <= j <= a.Length0 - 1 - i
      invariant partitioned(a, i - 1)
      invariant sorted(a, i + j + 1, a.Length0 - 1)
      invariant forall k :: i <= k < i + j ==> a[k, 1] <= a[i + j, 1]
    {
      if a[j, 1] > a[j + 1, 1] {
        // Swap rows j and j+1
        var temp0 := a[j, 0];
        var temp1 := a[j, 1];
        a[j, 0] := a[j + 1, 0];
        a[j, 1] := a[j + 1, 1];
        a[j + 1, 0] := temp0;
        a[j + 1, 1] := temp1;
        
        SortedMaintainedAfterSwap(a, j, i);
      }
      j := j + 1;
    }
    
    // After inner loop, the largest element in range [i..a.Length0-1-i] 
    // has bubbled to position a.Length0-1-i
    assert forall k :: i <= k < a.Length0 - 1 - i ==> a[k, 1] <= a[a.Length0 - 1 - i, 1];
    
    // Update partitioned property
    if i >= 0 {
        assert forall k, k' :: 0 <= k <= i < k' < a.Length0 ==> a[k, 1] <= a[k', 1];
    }
    
    i := i + 1;
  }
  
  BubbleCorrectness(a, i - 1);
}
// </vc-code>

// Predicates for Bubble Sort
predicate sorted(a: array2<int>, l: int, u: int)
    reads a
    requires a.Length1 == 2
{
    forall i, j :: 0 <= l <= i <= j <= u < a.Length0 ==> a[i, 1] <= a[j, 1]
}

predicate partitioned(a: array2<int>, i: int)
    reads a
    requires a.Length1 == 2
{
    forall k, k' :: 0 <= k <= i < k' < a.Length0 ==> a[k, 1] <= a[k', 1]
}