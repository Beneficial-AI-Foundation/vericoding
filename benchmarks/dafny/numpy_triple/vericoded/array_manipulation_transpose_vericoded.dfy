// <vc-preamble>
/*
 * Matrix transpose operations for 2D arrays.
 * This file implements numpy.transpose functionality for 2D matrices,
 * providing specifications for swapping rows and columns.
 */

// Type alias for a 2D matrix represented as sequence of sequences
type Matrix = seq<seq<real>>

// Predicate to check if a matrix is well-formed (rectangular)
predicate IsValidMatrix(m: Matrix, rows: nat, cols: nat)
{
    |m| == rows &&
    forall i :: 0 <= i < |m| ==> |m[i]| == cols
}

// Method to transpose a 2D matrix
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): fixed precondition for BuildTransposedRow to use >= instead of == */
function BuildTransposedRow(a: Matrix, col: nat, rows: nat): seq<real>
  requires rows > 0 ==> |a| >= rows
  requires rows > 0 ==> forall i :: 0 <= i < rows ==> |a[i]| > col
  ensures |BuildTransposedRow(a, col, rows)| == rows
  ensures rows > 0 ==> forall i :: 0 <= i < rows ==> BuildTransposedRow(a, col, rows)[i] == a[i][col]
  decreases rows
{
  if rows == 0 then []
  else BuildTransposedRow(a, col, rows - 1) + [a[rows - 1][col]]
}

function BuildTransposedMatrix(a: Matrix, rows: nat, cols: nat, builtCols: nat): Matrix
  requires rows > 0 && cols > 0 ==> IsValidMatrix(a, rows, cols)
  requires builtCols <= cols
  ensures |BuildTransposedMatrix(a, rows, cols, builtCols)| == builtCols
  ensures forall k :: 0 <= k < builtCols ==> |BuildTransposedMatrix(a, rows, cols, builtCols)[k]| == rows
  ensures rows > 0 && cols > 0 ==> forall i, j :: 0 <= i < rows && 0 <= j < builtCols ==> 
          BuildTransposedMatrix(a, rows, cols, builtCols)[j][i] == a[i][j]
  decreases builtCols
{
  if builtCols == 0 then []
  else BuildTransposedMatrix(a, rows, cols, builtCols - 1) + [BuildTransposedRow(a, builtCols - 1, rows)]
}
// </vc-helpers>

// <vc-spec>
method Transpose(a: Matrix, rows: nat, cols: nat) returns (result: Matrix)
    requires IsValidMatrix(a, rows, cols)
    ensures IsValidMatrix(result, cols, rows)
    ensures forall i, j :: 0 <= i < rows && 0 <= j < cols ==> 
            result[j][i] == a[i][j]
    ensures |result| == cols
    ensures forall k :: 0 <= k < |result| ==> |result[k]| == rows
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): use helper functions to build transposed matrix */
  if rows == 0 || cols == 0 {
    result := [];
    var i := 0;
    while i < cols
      invariant 0 <= i <= cols
      invariant |result| == i
      invariant forall k :: 0 <= k < i ==> |result[k]| == 0
    {
      result := result + [[]];
      i := i + 1;
    }
  } else {
    result := BuildTransposedMatrix(a, rows, cols, cols);
  }
}
// </vc-code>
