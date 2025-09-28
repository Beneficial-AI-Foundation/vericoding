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
function LegendreP(n: nat, z: real): real
{
    if n == 0 then 1.0
    else if n == 1 then z
    else ((2.0 * (n as real) - 1.0) * z * LegendreP(n - 1, z) - ((n as real) - 1.0) * LegendreP(n - 2, z)) / (n as real)
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
  var rows: seq<seq<real>> := [];
  var i := 0;
  while i < |x|
    invariant 0 <= i <= |x|
    invariant |rows| == i
    invariant forall k :: 0 <= k < i ==> |rows[k]| == deg + 1
    invariant forall k :: 0 <= k < i ==> rows[k][0] == 1.0
    invariant deg > 0 ==> forall k :: 0 <= k < i ==> rows[k][1] == x[k]
    invariant forall k, l :: 0 <= k < i && 0 <= l < |rows[k]| ==> rows[k][l] is real
  {
    var currentRow: seq<real> := [];
    var j := 0;
    while j <= deg
      invariant 0 <= j <= deg + 1
      invariant |currentRow| == j
      invariant forall k :: 0 <= k < j ==> currentRow[k] == LegendreP(k, x[i])
      invariant forall k :: 0 <= k < j ==> currentRow[k] is real
    {
      currentRow := currentRow + [LegendreP(j, x[i])];
      j := j + 1;
    }
    rows := rows + [currentRow];
    i := i + 1;
  }
  result := rows;
}
// </vc-code>
