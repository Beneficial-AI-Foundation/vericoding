// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added helper predicate to track if result is valid first occurrence */
predicate IsFirstOccurrence(arr: array<int>, target: int, index: int)
  reads arr
{
  0 <= index < arr.Length &&
  arr[index] == target &&
  forall i :: 0 <= i < index ==> arr[i] != target
}
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
  /* code modified by LLM (iteration 2): simplified to single linear search with proper invariants */
  result := -1;
  var i := 0;
  
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant result == -1 ==> forall j :: 0 <= j < i ==> arr[j] != target
    invariant result >= 0 ==> IsFirstOccurrence(arr, target, result) && result < i
  {
    if arr[i] == target {
      result := i;
      return;
    }
    i := i + 1;
  }
}
// </vc-code>
