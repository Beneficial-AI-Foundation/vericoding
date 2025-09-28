// <vc-preamble>
/*
 * Dafny specification for numpy.moveaxis operation on 1D arrays.
 * This captures the mathematical property that moving axes in a 1D vector
 * is always the identity operation since there is only one axis to move.
 * The specification ensures element preservation, size preservation, and
 * order preservation properties.
 */

// Method to move axes of a 1D array to new positions
// For 1D arrays, this is always the identity function since there's only one axis
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Fixed lemma syntax and simplified helpers */
function elementPreserved(a: seq<real>, result: seq<real>): bool
  requires |result| == |a|
{
  if |a| == 0 then true else
  (forall i :: 0 <= i < |a| ==> result[i] == a[i])
}

lemma moveaxis1DIdentityLemma(a: seq<real>, source: nat, dest: nat)
  ensures |a| == |a| && a == a
{
}

lemma orderPreservationLemma(a: seq<real>, result: seq<real>)
  requires result == a
  ensures forall i, j :: 0 <= i < j < |a| && a[i] <= a[j] ==> result[i] <= result[j]
{
}
// </vc-helpers>

// <vc-spec>
method moveaxis(a: seq<real>, source: nat, dest: nat) returns (result: seq<real>)
  ensures |result| == |a|  // Size preservation
  ensures forall i :: 0 <= i < |a| ==> result[i] == a[i]  // Element preservation
  ensures result == a  // Identity property for 1D arrays
  ensures forall i, j :: 0 <= i < j < |a| && a[i] <= a[j] ==> result[i] <= result[j]  // Order preservation
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): Simplified implementation returning identity */
  result := a;
  
  moveaxis1DIdentityLemma(a, source, dest);
  orderPreservationLemma(a, result);
}
// </vc-code>
