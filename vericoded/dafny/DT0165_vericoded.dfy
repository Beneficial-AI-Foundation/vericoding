// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

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
  var i := 1;
  while i < |arr|
    invariant 1 <= i <= |arr|
    invariant 0 <= idx < i
    invariant forall j :: 0 <= j < i ==> arr[j] <= arr[idx]
    invariant forall j :: 0 <= j < idx ==> arr[j] < arr[idx]
    invariant forall j :: 0 <= j < i && arr[j] == arr[idx] ==> idx <= j
  {
    if arr[i] > arr[idx] {
      idx := i;
    }
    i := i + 1;
  }
}
// </vc-code>
