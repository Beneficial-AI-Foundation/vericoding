// <vc-preamble>
// Helper function to compute the sum of element-wise products of two sequences
function SumProduct(a: seq<real>, b: seq<real>): real
  requires |a| == |b|
  decreases |a|
{
  if |a| == 0 then 0.0
  else a[0] * b[0] + SumProduct(a[1..], b[1..])
}

// Main tensor dot product method for 1-D vectors with axes=1
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method tensordot(a: seq<real>, b: seq<real>, axes: nat) returns (result: real)
  // Precondition: axes must be 1 for 1-D vector case
  requires axes == 1
  // Precondition: vectors must have same length
  requires |a| == |b|
  // Postcondition: result equals sum of element-wise products
  ensures result == SumProduct(a, b)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
