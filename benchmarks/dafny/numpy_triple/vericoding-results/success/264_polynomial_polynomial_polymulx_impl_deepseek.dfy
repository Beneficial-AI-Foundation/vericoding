// <vc-preamble>
/*
 * Polynomial multiplication by x operation.
 * This module provides functionality to multiply a polynomial by the independent variable x,
 * effectively shifting all coefficients one position higher and prepending a zero coefficient.
 */
// </vc-preamble>

// <vc-helpers>

// Helper function to construct the result sequence
function ConstructPolymulx(c: seq<real>): (r: seq<real>)
  requires |c| >= 0
  ensures |r| == |c| + 1
  ensures r[0] == 0.0
  ensures forall i :: 0 <= i < |c| ==> r[i + 1] == c[i]
{
  [0.0] + c
}

// </vc-helpers>

// <vc-spec>
method polymulx(c: seq<real>) returns (result: seq<real>)
    // Input polynomial coefficients ordered from low to high degree
    requires |c| >= 0
    // Output has exactly one more coefficient than input
    ensures |result| == |c| + 1
    // First coefficient of result is always 0 (no constant term after multiplication by x)
    ensures result[0] == 0.0
    // Remaining coefficients are the original coefficients shifted by one position
    // This represents multiplying p(x) by x to get x*p(x)
    ensures forall i :: 0 <= i < |c| ==> result[i + 1] == c[i]
// </vc-spec>
// <vc-code>
{
  result := [0.0] + c;
}
// </vc-code>
