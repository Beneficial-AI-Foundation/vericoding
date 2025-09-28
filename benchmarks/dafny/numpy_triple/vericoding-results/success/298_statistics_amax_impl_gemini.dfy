// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate IsFirstMax(s: seq<real>, n: nat, val: real, idx: nat)
  requires 0 < n <= |s|
  requires 0 <= idx < n
{
  s[idx] == val &&
  (forall j :: 0 <= j < n ==> s[j] <= val) &&
  (forall k :: 0 <= k < n && s[k] == val ==> idx <= k)
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
  result := a[0];
  var max_index := 0;
  var i := 1;
  while i < |a|
    invariant 1 <= i <= |a|
    invariant 0 <= max_index < i
    invariant IsFirstMax(a, i, result, max_index)
  {
    if a[i] > result {
      result := a[i];
      max_index := i;
    }
    i := i + 1;
  }
}
// </vc-code>
