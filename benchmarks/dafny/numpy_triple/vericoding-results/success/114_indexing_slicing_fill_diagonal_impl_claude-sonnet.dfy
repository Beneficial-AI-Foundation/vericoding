// <vc-preamble>
// Method to fill the main diagonal of a 2D matrix with a specified value
// </vc-preamble>

// <vc-helpers>
predicate IsRectangular<T>(mat: seq<seq<T>>)
{
  |mat| > 0 && forall i :: 0 <= i < |mat| ==> |mat[i]| == |mat[0]|
}

/* helper modified by LLM (iteration 2): added decreases clause to fix termination */
function UpdateDiagonal<T>(mat: seq<seq<T>>, val: T, row: int): seq<seq<T>>
  requires IsRectangular(mat)
  requires 0 <= row <= |mat|
  decreases |mat| - row
{
  if row == |mat| then mat
  else if row < |mat[0]| then
    UpdateDiagonal(mat[row := mat[row][row := val]], val, row + 1)
  else
    UpdateDiagonal(mat, val, row + 1)
}
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
  /* code modified by LLM (iteration 2): use imperative approach instead of recursive function */
  result := mat;
  var i := 0;
  while i < |result| && i < |result[0]|
    invariant 0 <= i <= |result|
    invariant |result| == |mat|
    invariant forall k :: 0 <= k < |result| ==> |result[k]| == |mat[0]|
    invariant forall k :: 0 <= k < i && k < |result[0]| ==> result[k][k] == val
    invariant forall k, j :: 0 <= k < |result| && 0 <= j < |result[0]| && k != j ==> result[k][j] == mat[k][j]
    invariant forall k :: i <= k < |result| && k < |result[0]| ==> result[k][k] == mat[k][k]
  {
    result := result[i := result[i][i := val]];
    i := i + 1;
  }
}
// </vc-code>
