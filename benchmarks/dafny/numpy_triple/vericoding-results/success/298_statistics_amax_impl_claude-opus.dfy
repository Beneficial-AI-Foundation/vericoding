// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method amax(a: seq<real>) returns (result: real)
  // Input must be non-empty
  requires |a| > 0
  
  // Core property: result is the maximum element in the sequence
  ensures exists max_idx :: 0 <= max_idx < |a| && result == a[max_idx]
  ensures forall i :: 0 <= i < |a| ==> a[i] <= result
  
  // Uniqueness: result is the first occurrence of the maximum value
  ensures exists first_max_idx :: (0 <= first_max_idx < |a| && 
          result == a[first_max_idx] &&
          (forall i :: 0 <= i < |a| && a[i] == result ==> first_max_idx <= i) &&
          (forall i :: 0 <= i < |a| ==> a[i] <= result))
  
  // For constant sequences, amax equals the constant value  
  ensures (forall i, j :: 0 <= i < |a| && 0 <= j < |a| ==> a[i] == a[j]) ==> 
          result == a[0]
  
  // Sanity check: the maximum value exists in the sequence
  ensures exists w :: 0 <= w < |a| && result == a[w]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Track index of first maximum occurrence */
  result := a[0];
  var first_max_idx := 0;
  var i := 1;
  while i < |a|
    invariant 1 <= i <= |a|
    invariant 0 <= first_max_idx < i
    invariant result == a[first_max_idx]
    invariant forall k :: 0 <= k < i ==> a[k] <= result
    invariant forall k :: 0 <= k < first_max_idx ==> a[k] < result
  {
    if a[i] > result {
      result := a[i];
      first_max_idx := i;
    }
    i := i + 1;
  }
}
// </vc-code>
