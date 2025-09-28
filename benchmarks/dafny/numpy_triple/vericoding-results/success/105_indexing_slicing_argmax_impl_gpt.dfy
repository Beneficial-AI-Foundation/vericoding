// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): define a simple minimum function for ints */
function helperMinInt(a: int, b: int): int { if a <= b then a else b }
// </vc-helpers>

// <vc-spec>
method argmax(arr: seq<real>) returns (idx: int)
  // Input must be non-empty to guarantee a maximum exists
  requires |arr| > 0
  
  // Output index is valid
  ensures 0 <= idx < |arr|
  
  // The returned index points to a maximum element
  ensures forall i :: 0 <= i < |arr| ==> arr[i] <= arr[idx]
  
  // All elements before the returned index are strictly less than the maximum
  ensures forall i :: 0 <= i < idx ==> arr[i] < arr[idx]
  
  // All elements after the returned index are less than or equal to the maximum
  ensures forall i :: idx < i < |arr| ==> arr[i] <= arr[idx]
  
  // The returned index is the first occurrence of the maximum value
  ensures forall j :: 0 <= j < |arr| && arr[j] == arr[idx] ==> idx <= j
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): iterate through sequence to find first index of maximum */
  var best: int := 0;
  var bestVal: real := arr[0];
  var i: int := 1;
  while i < |arr|
    invariant 0 <= best < i <= |arr|
    invariant bestVal == arr[best]
    invariant forall k :: 0 <= k < i ==> arr[k] <= bestVal
    invariant forall k :: 0 <= k < best ==> arr[k] < bestVal
    invariant forall j :: 0 <= j < i && arr[j] == bestVal ==> best <= j
    decreases |arr| - i
  {
    if bestVal < arr[i] {
      best := i;
      bestVal := arr[i];
    }
    i := i + 1;
  }
  idx := best;
}
// </vc-code>
