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
  var n := |c| - 1;
  mat := [];
  
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |mat| == i
    invariant forall k :: 0 <= k < i ==> |mat[k]| == n
    invariant forall k :: 0 <= k < i ==> mat[k][k] == 2.0 * (k as real) + 1.0
    invariant forall k :: 0 <= k < i && k < n - 1 ==> mat[k][k+1] == -((k as real) + 1.0)
    invariant forall k :: 1 <= k < i ==> mat[k][k-1] == -((k as real) + 1.0)
    invariant forall k, j :: 0 <= k < i && 0 <= j < n && !(j == k || j == k+1 || j == k-1) ==> mat[k][j] == 0.0
  {
    var row := [];
    var j := 0;
    while j < n
      invariant 0 <= j <= n
      invariant |row| == j
      invariant forall k :: 0 <= k < j && k == i ==> row[k] == 2.0 * (i as real) + 1.0
      invariant forall k :: 0 <= k < j && k == i + 1 ==> row[k] == -((i as real) + 1.0)
      invariant i > 0 && i - 1 < j ==> row[i-1] == -((i as real) + 1.0)
      invariant forall k :: 0 <= k < j && !(k == i || k == i+1 || k == i-1) ==> row[k] == 0.0
    {
      if j == i {
        row := row + [2.0 * (i as real) + 1.0];
      } else if j == i + 1 {
        row := row + [-((i as real) + 1.0)];
      } else if j == i - 1 && i > 0 {
        row := row + [-((i as real) + 1.0)];
      } else {
        row := row + [0.0];
      }
      j := j + 1;
    }
    mat := mat + [row];
    i := i + 1;
  }
}
// </vc-code>
