// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method TrimSeq(arr: array<real>) returns (result: array<real>)
  requires arr.Length >= 0
  ensures result.Length == arr.Length
  // If sequence is empty, return empty sequence
  ensures arr.Length == 0 ==> result.Length == 0
  // If last element is non-zero, return sequence unchanged
  ensures arr.Length > 0 && arr[arr.Length - 1] != 0.0 ==> 
    (forall i :: 0 <= i < arr.Length ==> result[i] == arr[i])
  // If last element is zero, trim properly
  ensures arr.Length > 0 && arr[arr.Length - 1] == 0.0 ==> 
    (exists k :: 0 <= k < arr.Length &&
      // All elements after k in original sequence are zero
      (forall j :: k < j < arr.Length ==> arr[j] == 0.0) &&
      // Result preserves elements up to k, zeros after
      (forall i :: 0 <= i <= k ==> result[i] == arr[i]) &&
      (forall i :: k < i < arr.Length ==> result[i] == 0.0) &&
      // Element at k is non-zero unless k = 0 and all elements are zero
      (k > 0 ==> arr[k] != 0.0) &&
      // If k = 0, then either arr[0] != 0 or all elements in arr are zero
      (k == 0 ==> (arr[0] != 0.0 || (forall j :: 0 <= j < arr.Length ==> arr[j] == 0.0))))
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
