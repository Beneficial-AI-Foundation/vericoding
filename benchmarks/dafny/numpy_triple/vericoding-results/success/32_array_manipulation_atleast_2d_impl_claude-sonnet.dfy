// <vc-preamble>
type Vector1D = seq<real>
type Matrix2D = seq<seq<real>>

/**
 * Converts a 1D vector to a 2D matrix with exactly one row.
 * The input vector becomes the single row of the resulting matrix.
 */
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method atleast_2d(arr: Vector1D) returns (result: Matrix2D)
    ensures |result| == 1  // Result has exactly 1 row
    ensures |result| > 0 ==> |result[0]| == |arr|  // Row has same length as input
    ensures |result| > 0 ==> result[0] == arr  // Single row matches input exactly
    ensures |result| > 0 ==> forall i :: 0 <= i < |arr| ==> result[0][i] == arr[i]  // Element preservation
// </vc-spec>
// <vc-code>
{
  result := [arr];
}
// </vc-code>
