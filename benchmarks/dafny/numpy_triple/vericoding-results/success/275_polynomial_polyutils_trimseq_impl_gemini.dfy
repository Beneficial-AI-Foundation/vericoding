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
  result := new real[arr.Length];
  if arr.Length > 0 {
    var k := arr.Length - 1;
    while k > 0 && arr[k] == 0.0
      invariant 0 <= k < arr.Length
      invariant forall j :: k < j < arr.Length ==> arr[j] == 0.0
    {
      k := k - 1;
    }

    var i := 0;
    while i <= k
      invariant 0 <= i <= k + 1
      invariant forall j :: 0 <= j < i ==> result[j] == arr[j]
    {
      result[i] := arr[i];
      i := i + 1;
    }

    while i < arr.Length
      invariant k < i <= arr.Length
      invariant forall j :: 0 <= j <= k ==> result[j] == arr[j]
      invariant forall j :: k < j < i ==> result[j] == 0.0
    {
      result[i] := 0.0;
      i := i + 1;
    }
  }
}
// </vc-code>
