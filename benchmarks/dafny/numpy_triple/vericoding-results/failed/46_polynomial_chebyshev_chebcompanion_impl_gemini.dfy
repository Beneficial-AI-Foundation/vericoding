// <vc-preamble>
ghost function sqrt(x: real): real
  requires x >= 0.0
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed syntax error in let-in expression */
function GetElement(c: seq<real>, n: int, i: int, j: int, s05: real): real
  requires |c| >= 2
  requires n == |c| - 2
  requires 0 <= i <= n && 0 <= j <= n
  requires c[|c|-1] != 0.0
  requires s05 * s05 == 0.5 && s05 >= 0.0
{
  if j == n then
    (let adjustment := (c[i] / c[|c|-1]) * 0.5
    in let baseValue := if i < n then (if i == 0 then -s05 else -0.5) else 0.0
    in baseValue - adjustment)
  else if j == i + 1 && i < n then
    if i == 0 then s05 else 0.5
  else if i == j + 1 && j < n then
    if j == 0 then s05 else 0.5
  else if i == j then
    0.0
  else
    0.0
}
// </vc-helpers>

// <vc-spec>
method ChebCompanion(c: seq<real>) returns (mat: seq<seq<real>>)
  // Input must have at least 2 elements to form a valid companion matrix
  requires |c| >= 2
  // The last coefficient must be non-zero to avoid division by zero
  requires c[|c|-1] != 0.0
  
  // Output matrix has dimensions (n+1) × (n+1) where n = |c| - 2
  ensures |mat| == |c| - 1
  ensures forall i {:trigger mat[i]} :: 0 <= i < |mat| ==> |mat[i]| == |c| - 1
  
  // Matrix structure properties for Chebyshev companion matrix
  ensures var n := |c| - 2;
  
    // Superdiagonal elements (positions [i][i+1] for i < n)
    (forall i {:trigger mat[i][i+1]} :: 0 <= i < n ==> mat[i][i+1] == 0.5) &&
    
    // Special case: first superdiagonal element when n > 0
    (n > 0 ==> mat[0][1] == sqrt(0.5)) &&
    
    // Subdiagonal elements (positions [i+1][i] for i < n) 
    (forall i {:trigger mat[i+1][i]} :: 0 <= i < n ==> mat[i+1][i] == 0.5) &&
    
    // Special case: first subdiagonal element when n > 0
    (n > 0 ==> mat[1][0] == sqrt(0.5)) &&
    
    // Main diagonal elements (except last column) are zero
    (forall i {:trigger mat[i]} :: 0 <= i <= n ==> 
      forall j {:trigger mat[i][j]} :: 0 <= j <= n && j != n ==> 
        (i == j ==> mat[i][j] == 0.0)) &&
    
    // Last column contains scaled coefficient ratios
    (forall i {:trigger mat[i][n]} :: 0 <= i <= n ==> 
      var adjustment := (c[i] / c[|c|-1]) * 0.5;
      var baseValue := if i < n then (if i == 0 then -sqrt(0.5) else -0.5) else 0.0;
      mat[i][n] == baseValue - adjustment) &&
    
    // All other elements not specified above are zero
    (forall i, j {:trigger mat[i][j]} :: 0 <= i <= n && 0 <= j <= n ==>
      (!(j == i + 1 && i < n) && // not superdiagonal
       !(i == j + 1 && j < n) && // not subdiagonal  
       !(j == n) &&              // not last column
       !(i == j))                // not main diagonal
      ==> mat[i][j] == 0.0)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): no changes made, previous logic retained */
  var n := |c| - 2;
  var s05: real :| s05 * s05 == 0.5 && s05 >= 0.0;
  mat := seq(n + 1, i => seq(n + 1, j => GetElement(c, n, i, j, s05)));
}
// </vc-code>
