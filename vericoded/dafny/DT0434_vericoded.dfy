// <vc-preamble>
// Method to compute the scaled companion matrix of Hermite polynomial coefficients
// Ghost function for square root (assumed to exist in the real number domain)
function Sqrt(x: real): real
  requires x >= 0.0
  ensures Sqrt(x) * Sqrt(x) == x
{
  assume {:axiom} false; 
  0.0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Correctly build matrix rows with proper indexing */
function BuildRow(i: int, n: int, c: seq<real>): seq<real>
  requires n >= 1
  requires |c| == n + 1
  requires 0 <= i < n
  requires c[n] != 0.0
  ensures |BuildRow(i, n, c)| == n
  ensures i < n - 1 ==> BuildRow(i, n, c)[i + 1] == Sqrt(0.5 * (i as real + 1.0))
  ensures i > 0 ==> BuildRow(i, n, c)[i - 1] == Sqrt(0.5 * (i as real))
  ensures BuildRow(i, n, c)[n - 1] == -c[i] / (2.0 * c[n]) * (if i == n - 1 then Sqrt(0.5 * ((n - 1) as real)) else 1.0)
  ensures forall j :: 0 <= j < n - 1 && j != i && j != i - 1 && j != i + 1 ==> BuildRow(i, n, c)[j] == 0.0
  ensures i != n - 1 ==> BuildRow(i, n, c)[i] == 0.0
{
  seq(n, j => 
    if i < n - 1 && j == i + 1 then Sqrt(0.5 * (i as real + 1.0))  // super-diagonal
    else if i > 0 && j == i - 1 then Sqrt(0.5 * (i as real))  // sub-diagonal
    else if j == n - 1 then  // last column
      -c[i] / (2.0 * c[n]) * (if i == n - 1 then Sqrt(0.5 * ((n - 1) as real)) else 1.0)
    else if i == j && i != n - 1 then 0.0  // diagonal is zero except possibly last row
    else 0.0  // all other entries
  )
}
// </vc-helpers>

// <vc-spec>
method HermCompanion(c: seq<real>) returns (mat: seq<seq<real>>)
  // Input must have at least 2 coefficients
  requires |c| >= 2
  // Leading coefficient must be non-zero
  requires c[|c|-1] != 0.0
  
  // Matrix dimensions are (n+1) x (n+1) where n = |c| - 2
  ensures |mat| == |c| - 1
  ensures forall i :: 0 <= i < |mat| ==> |mat[i]| == |c| - 1
  
  // Super-diagonal elements: mat[k][k+1] = sqrt(0.5 * (k+1)) for k = 0 to n-1
  ensures forall k {:trigger mat[k][k+1]} :: 0 <= k < |c| - 2 ==> 
    mat[k][k+1] == Sqrt(0.5 * (k as real + 1.0))
  
  // Sub-diagonal elements: mat[k+1][k] = sqrt(0.5 * (k+1)) for k = 0 to n-1  
  ensures forall k {:trigger mat[k+1][k]} :: 0 <= k < |c| - 2 ==> 
    mat[k+1][k] == Sqrt(0.5 * (k as real + 1.0))
  
  // Main diagonal is zero except possibly last row
  ensures forall i :: 0 <= i < |c| - 1 ==> 
    (i != |c| - 2) ==> mat[i][i] == 0.0
  
  // All other entries except last column are zero
  ensures forall i, j :: 0 <= i < |c| - 1 && 0 <= j < |c| - 2 ==>
    (i != j && i != j + 1 && i + 1 != j) ==> mat[i][j] == 0.0
  
  // Last column contains scaled coefficients
  ensures forall i :: 0 <= i < |c| - 1 ==>
    mat[i][|c| - 2] == -c[i] / (2.0 * c[|c| - 1]) * 
    (if i == |c| - 2 then Sqrt(0.5 * ((|c| - 2) as real)) else 1.0)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): Build matrix with verified row construction and fixed trigger warnings */
  var n := |c| - 1;
  mat := seq(n, i requires 0 <= i < n => BuildRow(i, n, c));
  
  // Assert properties to help the verifier with explicit triggers
  assert forall i :: 0 <= i < n ==> |mat[i]| == n;
  assert forall k {:trigger mat[k][k+1]} :: 0 <= k < n - 1 ==> mat[k][k+1] == Sqrt(0.5 * (k as real + 1.0));
  assert forall k {:trigger mat[k+1][k]} :: 0 <= k < n - 1 ==> mat[k+1][k] == Sqrt(0.5 * (k as real + 1.0));
  assert forall i :: 0 <= i < n ==> (i != n - 1) ==> mat[i][i] == 0.0;
  assert forall i, j :: 0 <= i < n && 0 <= j < n - 1 ==> (i != j && i != j + 1 && i + 1 != j) ==> mat[i][j] == 0.0;
  assert forall i :: 0 <= i < n ==> mat[i][n - 1] == -c[i] / (2.0 * c[n]) * (if i == n - 1 then Sqrt(0.5 * ((n - 1) as real)) else 1.0);
}
// </vc-code>
