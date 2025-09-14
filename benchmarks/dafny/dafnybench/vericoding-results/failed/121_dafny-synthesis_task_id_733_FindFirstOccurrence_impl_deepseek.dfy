

// <vc-helpers>
predicate IsSorted(arr: array<int>)
  reads arr
{
  forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
}

lemma BinarySearchLemma(arr: array<int>, target: int, low: int, high: int, mid: int, index: int)
  requires IsSorted(arr)
  requires 0 <= low <= high < arr.Length
  requires low <= mid <= high
  requires arr[mid] == target ==> index == mid
  requires arr[mid] < target ==> index == -1 || (index >= mid + 1 && index < arr.Length && arr[index] == target)
  requires arr[mid] > target ==> index == -1 || (index >= low && index <= mid - 1 && arr[index] == target)
  ensures 0 <= index < arr.Length ==> arr[index] == target
  ensures index == -1 ==> forall i :: 0 <= i < arr.Length ==> arr[i] != target
{
}

lemma SearchRangeLemma(arr: array<int>, target: int, low: int, high: int)
  requires IsSorted(arr)
  requires 0 <= low <= high + 1 <= arr.Length
  requires forall i :: 0 <= i < low ==> arr[i] != target
  requires forall i :: high < i < arr.Length ==> arr[i] != target
  ensures high < low ==> forall i :: 0 <= i < arr.Length ==> arr[i] != target
{
  if high < low {
    forall i | 0 <= i < arr.Length
      ensures arr[i] != target
    {
      if i < low {
        // already known from precondition
      } else if i > high {
        // already known from precondition
      } else {
        // i must be between low and high, but since high < low, this case is impossible
        assert false;
      }
    }
  }
}
// </vc-helpers>

// <vc-spec>
method FindFirstOccurrence(arr: array<int>, target: int) returns (index: int)
    requires arr != null
    requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
    ensures 0 <= index < arr.Length ==> arr[index] == target
    ensures index == -1 ==> forall i :: 0 <= i < arr.Length ==> arr[i] != target
    ensures forall i :: 0 <= i < arr.Length ==> arr[i] == old(arr[i])
// </vc-spec>
// <vc-code>
{
  var low := 0;
  var high := arr.Length - 1;
  index := -1;
  
  while low <= high
    invariant 0 <= low <= high + 1 <= arr.Length
    invariant forall i :: 0 <= i < low ==> arr[i] != target
    invariant forall i :: high < i < arr.Length ==> arr[i] != target
    invariant index == -1 || (0 <= index < arr.Length && arr[index] == target)
    decreases high - low
  {
    var mid := low + (high - low) / 2;
    
    if arr[mid] == target {
      index := mid;
      // Find the first occurrence by continuing to search left
      high := mid - 1;
    } else if arr[mid] < target {
      low := mid + 1;
    } else {
      high := mid - 1;
    }
  }
  
  // After the loop, if we found the target, we need to ensure it's the first occurrence
  if index != -1 {
    // Verify that all elements before index are not the target
    assert forall i :: 0 <= i < index ==> arr[i] != target;
  } else {
    SearchRangeLemma(arr, target, low, high);
  }
}
// </vc-code>

