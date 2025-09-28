// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function max(a: real, b: real): real { if a > b then a else b }
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
  idx := 0;
  var maxVal := arr[0];
  var i := 1;
  while i < |arr|
    invariant 0 <= idx < |arr|
    invariant 0 <= i <= |arr|
    invariant forall j :: 0 <= j < i ==> arr[j] <= maxVal
    invariant forall j :: 0 <= j < idx ==> arr[j] < maxVal
    invariant forall j :: idx < j < i ==> arr[j] <= maxVal
    invariant arr[idx] == maxVal
    invariant forall j :: 0 <= j < i && arr[j] == maxVal ==> idx <= j
  {
    if arr[i] > maxVal {
      maxVal := arr[i];
      idx := i;
    }
    i := i + 1;
  }
}
// </vc-code>
