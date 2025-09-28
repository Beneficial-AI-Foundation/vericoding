// <vc-preamble>
/*
 * Pseudo-Vandermonde matrix construction based on Legendre polynomials.
 * This module defines a method to construct a pseudo-Vandermonde matrix where each row
 * corresponds to a sample point and each column corresponds to evaluations of Legendre polynomials.
 */

// Method to construct a pseudo-Vandermonde matrix based on Legendre polynomials
// Takes sample points x and polynomial degree deg, returns matrix where V[i,j] = L_j(x[i])
// where L_j is the j-th Legendre polynomial
// </vc-preamble>

// <vc-helpers>
method computeLegendreRow(x: real, deg: nat) returns (row: seq<real>)
  ensures |row| == deg + 1
  ensures row[0] == 1.0
  ensures deg >= 1 ==> row[1] == x
{
  /* helper modified by LLM (iteration 4): fixed loop invariant issue by adding conditional for deg >= 2 */
  var leg: array<real> := new real[deg + 1];
  if deg + 1 > 0 {
    leg[0] := 1.0;
  }
  if deg >= 1 {
    leg[1] := x;
  }
  if deg >= 2 {
    var k := 2;
    while k <= deg
      invariant 2 <= k <= deg + 1
      invariant leg[0] == 1.0 && (deg >= 1 ==> leg[1] == x)
    {
      leg[k] := ((2 * k - 1) as real * x * leg[k - 1] - (k - 1) as real * leg[k - 2]) / k as real;
      k := k + 1;
    }
  }
  return leg[0..deg + 1];
}
// </vc-helpers>

// <vc-spec>
method legvander(x: seq<real>, deg: nat) returns (result: seq<seq<real>>)
  requires |x| >= 0
  ensures |result| == |x|  // Matrix has same number of rows as input points
  ensures forall i :: 0 <= i < |result| ==> |result[i]| == deg + 1  // Each row has deg+1 columns
  ensures forall i :: 0 <= i < |result| ==> result[i][0] == 1.0  // First column (L_0) is all ones
  ensures deg > 0 ==> forall i :: 0 <= i < |result| ==> result[i][1] == x[i]  // Second column (L_1) equals input when deg > 0
  ensures forall i, j :: 0 <= i < |result| && 0 <= j < |result[i]| ==> result[i][j] is real  // All entries are well-defined real numbers
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): maintained implementation as it satisfies postconditions */
  var V: seq<seq<real>> := [];
  var i := 0;
  while i < |x|
    invariant 0 <= i <= |x|
    invariant |V| == i
    invariant forall m :: 0 <= m < |V| ==> |V[m]| == deg + 1 && V[m][0] == 1.0 && (deg >= 1 ==> V[m][1] == x[m])
  {
    var row := computeLegendreRow(x[i], deg);
    V := V + [row];
    i := i + 1;
  }
  result := V;
}
// </vc-code>
