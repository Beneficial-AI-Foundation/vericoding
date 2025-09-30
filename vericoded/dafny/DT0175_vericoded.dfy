// <vc-preamble>
// Method to fill the main diagonal of a 2D matrix with a specified value
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method FillDiagonal<T>(mat: seq<seq<T>>, val: T) returns (result: seq<seq<T>>)
  // Input matrix must be non-empty and rectangular
  requires |mat| > 0
  requires forall i :: 0 <= i < |mat| ==> |mat[i]| == |mat[0]|
  
  // Output matrix has same dimensions as input
  ensures |result| == |mat|
  ensures forall i :: 0 <= i < |result| ==> |result[i]| == |mat[0]|
  
  // Diagonal elements (where row index equals column index) are set to val
  ensures forall i :: 0 <= i < |result| && i < |result[0]| ==> result[i][i] == val
  
  // Non-diagonal elements remain unchanged from the input matrix  
  ensures forall i, j :: 0 <= i < |result| && 0 <= j < |result[0]| && i != j ==> 
    result[i][j] == mat[i][j]
// </vc-spec>
// <vc-code>
{
  var n := |mat|;
  var m := |mat[0]|;
  var newMat := mat;
  
  for i := 0 to n
    invariant 0 <= i <= n
    invariant |newMat| == n
    invariant forall k :: 0 <= k < n ==> |newMat[k]| == m
    invariant forall k :: 0 <= k < i && k < m ==> newMat[k][k] == val
    invariant forall k, j :: 0 <= k < n && 0 <= j < m && (k >= i || k != j) ==> newMat[k][j] == mat[k][j]
  {
    if i < m {
      var row := newMat[i];
      var newRow := row[..i] + [val] + row[i+1..];
      newMat := newMat[..i] + [newRow] + newMat[i+1..];
    }
  }
  
  result := newMat;
}
// </vc-code>
