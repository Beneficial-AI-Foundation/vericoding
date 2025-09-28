// <vc-preamble>
// Method to fill the main diagonal of a 2D matrix with a specified value
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): no helpers are needed for this solution */

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
  /* code modified by LLM (iteration 4): using a loop with invariants to fix compilation error and prove correctness */
  result := mat;
  var i := 0;
  while i < |mat|
    decreases |mat| - i
    invariant 0 <= i <= |mat|
    invariant |result| == |mat|
    invariant forall k :: 0 <= k < |mat| ==> |result[k]| == |mat[0]|
    invariant forall k :: i <= k < |mat| ==> result[k] == mat[k]
    invariant forall k, j :: 0 <= k < i && 0 <= j < |mat[0]| && k != j ==> result[k][j] == mat[k][j]
    invariant forall k :: 0 <= k < i && k < |mat[0]| ==> result[k][k] == val
  {
    if i < |mat[0]| {
      var updated_row := result[i][i := val];
      result := result[i := updated_row];
    }
    i := i + 1;
  }
}
// </vc-code>
