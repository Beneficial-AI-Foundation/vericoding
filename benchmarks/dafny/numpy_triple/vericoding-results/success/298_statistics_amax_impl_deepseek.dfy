// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

lemma FindFirstMaxLemma(a: seq<real>, maxVal: real, first_index: int)
  requires |a| > 0
  requires 0 <= first_index < |a|
  requires a[first_index] == maxVal
  requires forall i :: 0 <= i < |a| ==> a[i] <= maxVal
  requires forall i :: 0 <= i < |a| && a[i] == maxVal ==> first_index <= i
  ensures exists first_max_idx :: (0 <= first_max_idx < |a| && 
          maxVal == a[first_max_idx] &&
          (forall i :: 0 <= i < |a| && a[i] == maxVal ==> first_max_idx <= i) &&
          (forall i :: 0 <= i < |a| ==> a[i] <= maxVal))
{
  /* helper modified by LLM (iteration 5): Fixed out of bounds access */
  assert 0 <= first_index < |a|;
  assert a[first_index] == maxVal;
  assert forall i :: 0 <= i < |a| && a[i] == maxVal ==> first_index <= i;
  assert forall i :: 0 <= i < |a| ==> a[i] <= maxVal;
}

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
  /* code modified by LLM (iteration 5): Fixed loop bounds and index checking */
  var idx: int := 0;
  result := a[0];
  
  var i: int := 1;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant 0 <= idx < |a|
    invariant result == a[idx]
    invariant forall j :: 0 <= j < i ==> a[j] <= result
    invariant exists j :: 0 <= j < i && result == a[j]
  {
    if a[i] > result {
      result := a[i];
      idx := i;
    }
    i := i + 1;
  }
  
  var first_max_idx: int := 0;
  while first_max_idx < |a| && a[first_max_idx] != result
    invariant 0 <= first_max_idx <= |a|
    invariant forall j :: 0 <= j < first_max_idx ==> a[j] != result
  {
    first_max_idx := first_max_idx + 1;
  }
  
  assert 0 <= first_max_idx < |a| && a[first_max_idx] == result;
  FindFirstMaxLemma(a, result, first_max_idx);
}
// </vc-code>
