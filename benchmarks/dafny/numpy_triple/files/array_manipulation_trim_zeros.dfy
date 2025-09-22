// <vc-preamble>
// Represents the trim mode for the trim_zeros function
datatype TrimMode = Front | Back | Both
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method TrimZeros(arr: seq<real>, mode: TrimMode) returns (result: seq<real>)
  ensures |result| <= |arr|
  // Result is a contiguous subsequence of the original array
  ensures exists start: nat, end: nat ::
    start <= end <= |arr| &&
    |result| == end - start &&
    (forall i :: 0 <= i < |result| ==> result[i] == arr[start + i])
  // If trimming from front, no leading zeros in result (unless result is empty)
  ensures (mode == Front || mode == Both) ==>
    (|result| == 0 || result[0] != 0.0)
  // If trimming from back, no trailing zeros in result (unless result is empty)  
  ensures (mode == Back || mode == Both) ==>
    (|result| == 0 || result[|result| - 1] != 0.0)
  // If trimming from front, all elements before the result were zeros
  ensures (mode == Front || mode == Both) ==>
    exists start: nat ::
      start <= |arr| &&
      |result| == |arr| - start &&
      (forall i :: 0 <= i < start ==> arr[i] == 0.0) &&
      (forall i :: 0 <= i < |result| ==> result[i] == arr[start + i]) &&
      (start == |arr| || arr[start] != 0.0)
  // If trimming from back, all elements after the result were zeros
  ensures (mode == Back || mode == Both) ==>
    exists end: nat ::
      end <= |arr| &&
      |result| == end &&
      (forall i :: end <= i < |arr| ==> arr[i] == 0.0) &&
      (forall i :: 0 <= i < |result| ==> result[i] == arr[i]) &&
      (end == 0 || arr[end - 1] != 0.0)
  // For Both mode, combines front and back trimming properties
  ensures mode == Both ==>
    exists start: nat, end: nat ::
      start <= end <= |arr| &&
      |result| == end - start &&
      (forall i :: 0 <= i < start ==> arr[i] == 0.0) &&
      (forall i :: end <= i < |arr| ==> arr[i] == 0.0) &&
      (forall i :: 0 <= i < |result| ==> result[i] == arr[start + i]) &&
      (start == |arr| || arr[start] != 0.0) &&
      (end == 0 || arr[end - 1] != 0.0)
  // For Front mode only, preserve trailing elements
  ensures mode == Front ==>
    exists start: nat ::
      start <= |arr| &&
      |result| == |arr| - start &&
      (forall i :: 0 <= i < start ==> arr[i] == 0.0) &&
      (forall i :: 0 <= i < |result| ==> result[i] == arr[start + i]) &&
      (start == |arr| || arr[start] != 0.0)
  // For Back mode only, preserve leading elements  
  ensures mode == Back ==>
    exists end: nat ::
      end <= |arr| &&
      |result| == end &&
      (forall i :: end <= i < |arr| ==> arr[i] == 0.0) &&
      (forall i :: 0 <= i < |result| ==> result[i] == arr[i]) &&
      (end == 0 || arr[end - 1] != 0.0)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
