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
/* helper modified by LLM (iteration 3): Legendre recurrence step */
function legendreNext(j: nat, x: real, pj: real, pm1: real): real
  requires j >= 1
{
  ((2.0 * (j as real) + 1.0) * x * pj - (j as real) * pm1) / ((j as real) + 1.0)
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
  /* code modified by LLM (iteration 3): construct result row-by-row using a temporary array and append slices */
  var n := |x|;
  var res: seq<seq<real>> := [];
  var i: nat := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |res| == i
    invariant forall k :: 0 <= k < i ==> |res[k]| == deg + 1
    invariant forall k :: 0 <= k < i ==> res[k][0] == 1.0
    invariant deg > 0 ==> forall k :: 0 <= k < i ==> res[k][1] == x[k]
    decreases n - i
  {
    var row := new real[deg + 1];
    row[0] := 1.0;
    if deg > 0 {
      row[1] := x[i];
      var j: nat := 1;
      while j < deg
        invariant 1 <= j <= deg
        invariant row.Length == deg + 1
        invariant row[0] == 1.0
        invariant deg > 0 ==> row[1] == x[i]
        decreases deg - j
      {
        var next := legendreNext(j, x[i], row[j], row[j - 1]);
        row[j + 1] := next;
        j := j + 1;
      }
    }
    res := res + [row[..]];
    i := i + 1;
  }
  result := res;
}
// </vc-code>
