// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): fixed MaxExists lemma with proof by contradiction and added FirstMaxIndex */
lemma MaxExists(arr: seq<real>) requires |arr| > 0 ensures exists i :: 0 <= i < |arr| && forall j :: 0 <= j < |arr| ==> arr[j] <= arr[i] {
  var max := arr[0];
  var maxIndex := 0;
  var k := 1;
  
  while k < |arr|
    invariant 0 <= maxIndex < |arr|
    invariant max == arr[maxIndex]
    invariant 0 <= k <= |arr|
    invariant forall j :: 0 <= j < k ==> arr[j] <= max
  {
    if arr[k] > max {
      max := arr[k];
      maxIndex := k;
    }
    k := k + 1;
  }
  
  // Prove the universal property
  assert forall j :: 0 <= j < |arr| ==> arr[j] <= arr[maxIndex];
}

lemma FirstMaxIndex(arr: seq<real>, maxVal: real) returns (idx: int)
  requires |arr| > 0
  requires exists i :: 0 <= i < |arr| && arr[i] == maxVal
  ensures 0 <= idx < |arr|
  ensures arr[idx] == maxVal
  ensures forall j :: 0 <= j < |arr| && arr[j] == maxVal ==> idx <= j
{
  idx := 0;
  
  // Find the first occurrence of maxVal
  while idx < |arr| && arr[idx] != maxVal
    invariant 0 <= idx <= |arr|
    invariant forall j :: 0 <= j < idx ==> arr[j] != maxVal
  {
    idx := idx + 1;
  }
  
  assert arr[idx] == maxVal;
}
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
  /* code modified by LLM (iteration 4): updated implementation with proper logic */
  var maxVal := arr[0];
  idx := 0;
  var i := 1;
  
  while i < |arr|
    invariant 0 <= idx < |arr|
    invariant maxVal == arr[idx]
    invariant 0 <= i <= |arr|
    invariant forall j :: 0 <= j < i ==> arr[j] <= maxVal
    invariant forall j :: 0 <= j < idx ==> arr[j] < maxVal
    invariant forall k :: 0 <= k < i && arr[k] == maxVal ==> idx <= k
  {
    if arr[i] > maxVal {
      maxVal := arr[i];
      idx := i;
    } else if arr[i] == maxVal {
      // If equal and i comes before current idx, update to keep first occurrence
      if i < idx {
        idx := i;
      }
    }
    i := i + 1;
  }
}
// </vc-code>
