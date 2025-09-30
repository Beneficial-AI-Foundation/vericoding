// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate HasTarget(arr: array<int>, target: int, n: int)
  requires 0 <= n <= arr.Length
  reads arr
{
  exists k :: 0 <= k < n && arr[k] == target
}

lemma BinarySearchCorrectness(arr: array<int>, target: int, low: int, high: int, mid: int)
  requires 0 <= low <= high < arr.Length
  requires mid == low + (high - low) / 2
  requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
  requires forall k :: 0 <= k < low ==> arr[k] != target
  ensures arr[mid] < target ==> forall k :: low <= k <= mid ==> arr[k] != target
{
  if arr[mid] < target {
    var k := low;
    while k <= mid
      invariant low <= k <= mid + 1
      invariant forall j :: low <= j < k ==> arr[j] != target
    {
      if arr[k] == target {
        assert arr[k] == target && arr[mid] < target;
        assert k <= mid;
        assert false;
      }
      k := k + 1;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method FindFirstOccurrence(arr: array<int>, target: int) returns (index: int)

    requires
        forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]

    ensures
        if index >= 0 then (
            && 0 <= index < arr.Length
            && (forall k :: 0 <= k < index ==> arr[k] != target)
            && arr[index] == target
        ) else (
            forall k :: 0 <= k < arr.Length ==> arr[k] != target
        )
// </vc-spec>
// <vc-code>
{
  var low := 0;
  var high := arr.Length - 1;
  
  while low <= high
    invariant 0 <= low <= arr.Length
    invariant -1 <= high < arr.Length
    invariant forall k :: 0 <= k < low ==> arr[k] != target
    invariant high < arr.Length - 1 ==> forall k :: high < k < arr.Length ==> arr[k] != target
    invariant forall k :: 0 <= k < arr.Length && arr[k] == target ==> low <= k <= high || k == low - 1
  {
    var mid := low + (high - low) / 2;
    
    if arr[mid] == target {
      var result := mid;
      while result > 0 && arr[result - 1] == target
        invariant 0 <= result <= mid
        invariant arr[result] == target
        invariant forall k :: result < k <= mid ==> arr[k] == target
      {
        result := result - 1;
      }
      index := result;
      return;
    } else if arr[mid] < target {
      BinarySearchCorrectness(arr, target, low, high, mid);
      low := mid + 1;
    } else {
      high := mid - 1;
    }
  }
  
  index := -1;
}
// </vc-code>
