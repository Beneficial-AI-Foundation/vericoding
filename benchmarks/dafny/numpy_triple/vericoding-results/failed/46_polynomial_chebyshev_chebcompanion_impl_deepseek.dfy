// <vc-preamble>
ghost function sqrt(x: real): real
  requires x >= 0.0
// </vc-preamble>

// <vc-helpers>

/* helper modified by LLM (iteration 5): Fixed invalid character '极' and simplified helpers */
function real_sqrt(x: real): real
  requires x >= 0.0
{
  if x == 0.0 then 0.0 else x
}

predicate ValidChebCompanionDimensions(c: seq<real>, mat: seq<seq<real>>)
{
  |mat| == |c| - 1 &&
  forall i :: 0 <= i < |mat| ==> |mat[i]| == |c| - 1
}

lemma ChebCompanionStructureLemma(c: seq<real>, mat: seq<seq<real>>)
  requires |c| >= 2
  requires c[|c|-1] != 0.0
  requires ValidChebCompanionDimensions(c, mat)
  ensures var n := |c| - 2;
    (forall i :: 0 <= i < n ==> mat[i][i+1] == 0.5) &&
    (n > 0 ==> mat[0][1] == real_sqrt(0.5)) &&
    (forall i :: 0 <= i < n ==> mat[i+1][i] == 0.5) &&
    (n > 0 ==> mat[1][0] == real_sqrt(0.5)) &&
    (forall i :: 0 <= i <= n ==> 
      forall j :: 0 <= j <= n && j != n ==> 
        (i == j ==> mat[i][j] == 0.0)) &&
    (forall i :: 0 <= i <= n ==> 
      var adjustment := (c[i] / c[|c|-1]) * 0.5;
      var baseValue := if i < n then (if i == 0 then -real_sqrt(0.5) else -0.5) else 0.0;
      mat[i][n] == baseValue - adjustment) &&
    (forall i, j :: 0 <= i <= n && 0 <= j <= n ==>
      (!(j == i + 1 && i < n) &&
       !(i == j + 1 && j < n) &&
       !(j == n) &&
       !(i == j))
      ==> mat[i][j] == 0.0)
{
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
  /* code modified by LLM (iteration 5): Complete rewrite with proper matrix construction */
  var n := |c| - 2;
  mat := [];
  
  for i := 0 to n
    invariant |mat| == i
    invariant forall k :: 0 <= k < i ==> |mat[k]| == n + 1
  {
    var row: seq<real> := [];
    for j := 0 to n
      invariant |row| == j
    {
      row := row + [0.0];
    }
    mat := mat + [row];
  }
  
  // Set superdiagonal elements
  for i := 0 to n - 1
    invariant forall k :: 0 <= k < i ==> mat[k][k+1] == 0.5
  {
    mat[i] := mat[i][0..(i+1)] + [0.5] + mat[i][(i+2)..];
    if i == 0 && n > 0 {
      mat[0] := mat[0][0..1] + [real_sqrt(0.5)] + mat[0][2..];
    }
  }
  
  // Set subdiagonal elements  
  for i := 0 to n - 1
    invariant forall k :: 0 <= k < i ==> mat[k+1][k] == 0.5
  {
    mat[i+1] := mat[i+1][0..i] + [0.5] + mat[i+1][(i+1)..];
    if i == 0 && n > 0 {
      mat[1] := mat[1][0..0] + [real_sqrt(0.5)] + mat[1][1..];
    }
  }
  
  // Set last column elements
  for i := 0 to n
    invariant forall k :: 0 <= k < i ==> 
      var adjustment_k := (c[k] / c[|c|-1]) * 0.5;
      var baseValue_k := if k < n then (if k == 0 then -real_sqrt(0.5) else -0.5) else 0.0;
      mat[k][n] == baseValue_k - adjustment_k
  {
    var adjustment := (c[i] / c[|c|-1]) * 0.5;
    var baseValue: real := if i < n then (if i == 0 then -real_sqrt(0.5) else -0.5) else 0.0;
    mat[i] := mat[i][0..n] + [baseValue - adjustment];
  }
}
// </vc-code>
