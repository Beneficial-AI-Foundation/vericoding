// <vc-preamble>
// Method to flatten a 2D matrix into a 1D vector using row-major order
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Flatten(mat: seq<seq<real>>) returns (result: seq<real>)
  // Precondition: matrix must be rectangular (all rows have the same length)
  requires |mat| == 0 || forall i :: 0 <= i < |mat| ==> |mat[i]| == |mat[0]|
  
  // Postcondition: result length equals rows * cols  
  ensures |result| == |mat| * (if |mat| == 0 then 0 else |mat[0]|)
  
  // Postcondition: elements are preserved in row-major order
  ensures |mat| > 0 ==> forall row, col :: 0 <= row < |mat| && 0 <= col < |mat[0]| ==>
    result[row * |mat[0]| + col] == mat[row][col]
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
