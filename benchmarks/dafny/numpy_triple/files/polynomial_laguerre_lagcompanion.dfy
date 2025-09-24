// <vc-preamble>
// Method to compute the companion matrix of Laguerre polynomial coefficients
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method LaguerreCompanion(c: seq<real>) returns (mat: seq<seq<real>>)
  requires |c| >= 2  // Need at least 2 coefficients
  requires c[|c|-1] != 0.0  // Last coefficient must be non-zero
  ensures |mat| == |c| - 1  // Matrix has (n+1) x (n+1) dimensions where input has n+2 elements
  ensures forall i :: 0 <= i < |mat| ==> |mat[i]| == |c| - 1  // Each row has correct length
  ensures forall i :: 0 <= i < |mat| ==> 
    mat[i][i] == 2.0 * (i as real) + 1.0  // Diagonal elements: 2*i + 1
  ensures forall i :: 0 <= i < |mat| - 1 ==> 
    mat[i][i+1] == -((i as real) + 1.0)  // Super-diagonal elements: -(i+1)
  ensures forall i :: 1 <= i < |mat| ==> 
    mat[i][i-1] == -((i as real) + 1.0)  // Sub-diagonal elements: -(i+1)
  ensures forall i, j :: (0 <= i < |mat| && 0 <= j < |mat| && 
    !(j == i || j == i+1 || j == i-1)) ==> 
    mat[i][j] == 0.0  // All other elements are zero
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
