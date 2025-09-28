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
  /* code modified by LLM (iteration 2): Initialize matrix first, then update elements to maintain invariants */
  var n := |c| - 1;
  mat := seq(n, i => seq(n, j => 0.0));
  
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |mat| == n
    invariant forall k :: 0 <= k < |mat| ==> |mat[k]| == n
    invariant forall k :: 0 <= k < i ==> mat[k][k] == 2.0 * (k as real) + 1.0
    invariant forall k :: 0 <= k < i && k < n - 1 ==> mat[k][k+1] == -((k as real) + 1.0)
    invariant forall k :: 1 <= k < i ==> mat[k][k-1] == -((k as real) + 1.0)
    invariant forall k, l :: (0 <= k < i && 0 <= l < n && !(l == k || l == k+1 || l == k-1)) ==> mat[k][l] == 0.0
    invariant forall k, l :: (i <= k < n && 0 <= l < n) ==> mat[k][l] == 0.0
  {
    var newRow := seq(n, j => 0.0);
    newRow := newRow[i := 2.0 * (i as real) + 1.0];
    
    if i < n - 1 {
      newRow := newRow[i+1 := -((i as real) + 1.0)];
    }
    
    if i > 0 {
      newRow := newRow[i-1 := -((i as real) + 1.0)];
    }
    
    mat := mat[i := newRow];
    i := i + 1;
  }
}
// </vc-code>
