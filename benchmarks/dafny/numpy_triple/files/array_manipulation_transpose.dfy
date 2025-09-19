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
  assume {:axiom} false;
}
// </vc-code>
