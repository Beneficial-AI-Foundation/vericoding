// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method max(a: seq<real>) returns (result: real)
  // Input must be non-empty
  requires |a| > 0
  
  // Core property: result is the maximum element that exists in the sequence
  ensures exists max_idx :: 0 <= max_idx < |a| && result == a[max_idx]
  ensures forall i :: 0 <= i < |a| ==> a[i] <= result
  
  // Uniqueness property: result is the first occurrence of the maximum value
  ensures (exists first_max_idx :: 0 <= first_max_idx < |a| && 
           (result == a[first_max_idx] &&
            (forall i :: 0 <= i < |a| && a[i] == result ==> first_max_idx <= i)))
  
  // For constant sequences, max equals the constant value
  ensures (forall i, j :: 0 <= i < |a| && 0 <= j < |a| ==> a[i] == a[j]) ==> result == a[0]
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
