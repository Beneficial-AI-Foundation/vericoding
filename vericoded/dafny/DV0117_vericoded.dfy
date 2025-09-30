// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method FindFirstOccurrence(arr: array<int>, target: int) returns (result: int)
    requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
    ensures (result >= 0 ==> (
        0 <= result < arr.Length &&
        arr[result] == target &&
        forall i :: 0 <= i < result ==> arr[i] != target
    )) &&
    (result == -1 ==> (
        forall i :: 0 <= i < arr.Length ==> arr[i] != target
    ))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): strengthened loop invariants to prove postconditions */
  var left := 0;
  var right := arr.Length;
  result := -1;
  
  while left < right
    invariant 0 <= left <= right <= arr.Length
    invariant result == -1 || (0 <= result < arr.Length && arr[result] == target)
    invariant forall i :: 0 <= i < left ==> arr[i] < target
    invariant forall i :: right <= i < arr.Length ==> arr[i] > target || (arr[i] == target && result != -1 && result <= i)
    invariant result != -1 ==> result >= left && result < arr.Length && arr[result] == target
    invariant result != -1 ==> forall i :: 0 <= i < left ==> arr[i] != target
  {
    var mid := left + (right - left) / 2;
    
    if arr[mid] == target {
      result := mid;
      right := mid;
    } else if arr[mid] < target {
      left := mid + 1;
    } else {
      right := mid;
    }
  }
  
  if result == -1 {
    assert left == right;
    assert forall i :: 0 <= i < left ==> arr[i] < target;
    assert forall i :: right <= i < arr.Length ==> arr[i] > target;
    assert forall i :: 0 <= i < arr.Length ==> arr[i] != target;
  } else {
    assert forall i :: 0 <= i < result ==> i < left || arr[i] < target;
    assert forall i :: 0 <= i < result ==> arr[i] != target;
  }
}
// </vc-code>
