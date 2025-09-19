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
  assume {:axiom} false;
}
// </vc-code>
