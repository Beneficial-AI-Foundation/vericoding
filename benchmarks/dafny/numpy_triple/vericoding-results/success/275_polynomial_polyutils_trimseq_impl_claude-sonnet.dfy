// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): helper to check if all elements from index onwards are zero */
function AllZerosFrom(arr: array<real>, start: int): bool
  requires 0 <= start <= arr.Length
  reads arr
{
  forall j :: start <= j < arr.Length ==> arr[j] == 0.0
}

/* helper modified by LLM (iteration 2): helper to check if all elements in array are zero */
function AllZeros(arr: array<real>): bool
  reads arr
{
  forall j :: 0 <= j < arr.Length ==> arr[j] == 0.0
}
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
  /* code modified by LLM (iteration 2): witness k explicitly for postcondition */
  result := new real[arr.Length];
  
  if arr.Length == 0 {
    return;
  }
  
  // Copy all elements first
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant forall j :: 0 <= j < i ==> result[j] == arr[j]
  {
    result[i] := arr[i];
    i := i + 1;
  }
  
  // If last element is non-zero, we're done
  if arr[arr.Length - 1] != 0.0 {
    return;
  }
  
  // Find the rightmost non-zero element
  var k := arr.Length - 1;
  while k > 0 && arr[k] == 0.0
    invariant 0 <= k < arr.Length
    invariant forall j :: k < j < arr.Length ==> arr[j] == 0.0
  {
    k := k - 1;
  }
  
  // Zero out elements after k
  var j := k + 1;
  while j < arr.Length
    invariant k < j <= arr.Length
    invariant forall m :: 0 <= m <= k ==> result[m] == arr[m]
    invariant forall m :: k < m < j ==> result[m] == 0.0
  {
    result[j] := 0.0;
    j := j + 1;
  }
  
  // Witness k for the postcondition
  assert forall j :: k < j < arr.Length ==> arr[j] == 0.0;
  assert forall i :: 0 <= i <= k ==> result[i] == arr[i];
  assert forall i :: k < i < arr.Length ==> result[i] == 0.0;
  
  if k > 0 {
    assert arr[k] != 0.0;
  } else {
    if arr[0] == 0.0 {
      assert forall j :: 0 <= j < arr.Length ==> arr[j] == 0.0;
    }
  }
}
// </vc-code>
