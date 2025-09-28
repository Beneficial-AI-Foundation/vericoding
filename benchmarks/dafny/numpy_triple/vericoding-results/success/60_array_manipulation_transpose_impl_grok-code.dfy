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
  /* code modified by LLM (iteration 2): Added loop invariants to prove postconditions for matrix transpose */
  var temp: Matrix := [];
  for j := 0 to cols
    invariant |temp| == j
    invariant forall x :: 0 <= x < j ==> (|temp[x]| == rows && forall y :: 0 <= y < rows ==> temp[x][y] == a[y][x])
  {
    var newRow: seq<real> := [];
    for i := 0 to rows
      invariant |newRow| == i
      invariant forall z :: 0 <= z < i ==> newRow[z] == a[z][j]
    {
      newRow := newRow + [a[i][j]];
    }
    temp := temp + [newRow];
  }
  result := temp;
}
// </vc-code>
