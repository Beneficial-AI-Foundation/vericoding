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
  if |a| == 0 { } else {
    var max_val := a[0];
    var first_idx := 0;
    var i := 1;
    while i < |a|
      invariant 1 <= i <= |a|
      invariant 0 <= first_idx < i
      invariant max_val == a[first_idx]
      invariant forall j :: 0 <= j < i ==> a[j] <= max_val
      invariant forall j :: 0 <= j < i && a[j] == max_val ==> first_idx <= j
    {
      if a[i] > max_val {
        max_val := a[i];
        first_idx := i;
      }
      i := i + 1;
    }
    result := max_val;
  }
}
// </vc-code>
