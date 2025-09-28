// <vc-preamble>
// Method to compute the companion matrix of Laguerre polynomial coefficients
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): [simplified function by removing redundant postcondition] */
function GenerateRow(i: int, n: int): (res: seq<real>)
  requires 0 <= n
  requires 0 <= i < n
  ensures |res| == n
{
  seq(n, j =>
    if j == i then 2.0 * (i as real) + 1.0
    else if j == i + 1 then -((i as real) + 1.0)
    else if j == i - 1 then -((i as real) + 1.0)
    else 0.0
  )
}
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
  /* code modified by LLM (iteration 3): [use a while loop to prove the helper's precondition] */
  var n := |c| - 1;
  mat := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |mat| == i
    invariant forall k :: 0 <= k < i ==> mat[k] == GenerateRow(k, n)
  {
    mat := mat + [GenerateRow(i, n)];
    i := i + 1;
  }
}
// </vc-code>
