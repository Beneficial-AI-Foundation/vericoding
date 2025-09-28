// <vc-preamble>
// Method to construct the companion matrix of a polynomial
// Given coefficients c = [c0, c1, ..., cn, c_{n+1}] representing polynomial
// p(x) = c0 + c1*x + ... + c_{n+1}*x^{n+1}, returns the (n+1)×(n+1) companion matrix
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method PolyCompanion(c: seq<real>) returns (matrix: seq<seq<real>>)
    requires |c| >= 2  // Need at least 2 coefficients
    requires c[|c|-1] != 0.0  // Leading coefficient must be non-zero
    ensures |matrix| == |c| - 1  // Matrix is (n+1)×(n+1) for degree n+1 polynomial
    ensures forall i :: 0 <= i < |matrix| ==> |matrix[i]| == |c| - 1  // Square matrix
    ensures forall i, j :: 0 <= i < |matrix| - 1 && 0 <= j < |matrix[i]| ==>
        // First n rows: shifted identity pattern (1 in position i+1, 0 elsewhere)
        (matrix[i][j] == (if j == i + 1 then 1.0 else 0.0))
    ensures forall j :: 0 <= j < |matrix| - 1 ==>
        // Last row: normalized negative coefficients
        matrix[|matrix| - 1][j] == -c[j] / c[|c| - 1]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Added trigger to quantifier in loop invariant */
  var n := |c| - 1;
  matrix := seq(n, i => seq(n, j => 0.0));
  
  // Set up first n-1 rows with shifted identity pattern
  var i := 0;
  while i < n - 1
    invariant 0 <= i <= n - 1
    invariant |matrix| == n
    invariant forall k :: 0 <= k < |matrix| ==> |matrix[k]| == n
    invariant forall r, c :: 0 <= r < i && 0 <= c < n ==> matrix[r][c] == (if c == r + 1 then 1.0 else 0.0)
    invariant forall r, c :: i <= r < n && 0 <= c < n ==> matrix[r][c] == 0.0
  {
    matrix := matrix[i := matrix[i][i + 1 := 1.0]];
    i := i + 1;
  }
  
  // Set up last row with normalized negative coefficients
  var j := 0;
  while j < n
    invariant 0 <= j <= n
    invariant |matrix| == n
    invariant forall k :: 0 <= k < |matrix| ==> |matrix[k]| == n
    invariant forall r, c :: 0 <= r < n - 1 && 0 <= c < n ==> matrix[r][c] == (if c == r + 1 then 1.0 else 0.0)
    invariant forall k {:trigger matrix[n - 1][k]} :: 0 <= k < j ==> matrix[n - 1][k] == -c[k] / c[|c| - 1]
    invariant forall k {:trigger matrix[n - 1][k]} :: j <= k < n ==> matrix[n - 1][k] == 0.0
  {
    matrix := matrix[n - 1 := matrix[n - 1][j := -c[j] / c[|c| - 1]]];
    j := j + 1;
  }
}
// </vc-code>
