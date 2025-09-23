// <vc-preamble>
// Method to compute the scaled companion matrix of Legendre series coefficients
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method legcompanion(c: seq<real>) returns (result: seq<seq<real>>)
  // Input must have at least 2 coefficients to form a meaningful companion matrix
  requires |c| >= 2
  // The leading coefficient (last element) must be non-zero for well-defined companion matrix
  requires c[|c|-1] != 0.0
  
  // The result is a square matrix of dimension (|c|-1) x (|c|-1)
  ensures |result| == |c| - 1
  // Each row has the correct length to form a square matrix
  ensures forall i :: 0 <= i < |result| ==> |result[i]| == |c| - 1
  // The companion matrix is symmetric: result[i][j] == result[j][i]
  ensures forall i, j :: 0 <= i < |result| && 0 <= j < |result| ==> result[i][j] == result[j][i]
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
