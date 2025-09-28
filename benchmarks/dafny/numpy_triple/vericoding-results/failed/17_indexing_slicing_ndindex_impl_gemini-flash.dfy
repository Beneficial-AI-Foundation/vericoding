// <vc-preamble>
/*
 * N-dimensional index generation for arrays
 * 
 * This module provides functionality to generate all valid N-dimensional indices
 * for an array with a given shape, following C-order (row-major) iteration.
 * For a 2D array with shape (m, n), this generates all index pairs (i, j) 
 * where 0 ≤ i < m and 0 ≤ j < n in the order where the last dimension changes fastest.
 */

// Method to generate all N-dimensional indices for a given 2D array shape
// Returns a sequence of index pairs in C-order (row-major order)
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ndindex(shape: (nat, nat)) returns (indices: seq<(nat, nat)>)
  requires shape.0 >= 0 && shape.1 >= 0
  // The result contains exactly m*n index pairs for shape (m, n)
  ensures |indices| == shape.0 * shape.1
  // Each index pair (i, j) satisfies the bounds: 0 ≤ i < m and 0 ≤ j < n
  ensures forall k :: 0 <= k < |indices| ==> 
    indices[k].0 < shape.0 && indices[k].1 < shape.1
  // All possible valid indices are included exactly once
  ensures forall i, j :: 0 <= i < shape.0 && 0 <= j < shape.1 ==>
    exists k :: 0 <= k < |indices| && indices[k] == (i, j)
  // The indices are generated in C-order: k = i * n + j where (i, j) = indices[k]
  ensures forall k :: 0 <= k < |indices| ==>
    k == indices[k].0 * shape.1 + indices[k].1
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Add invariant to ensure the first element of indices[k] is less than m */
{
  var m := shape.0;
  var n := shape.1;
  var currentIndices: seq<(nat, nat)> := [];

  var i := 0;
  while i < m
    invariant 0 <= i <= m
    invariant |currentIndices| == i * n
    invariant forall k :: 0 <= k < |currentIndices| ==> 0 <= currentIndices[k].0 < i && 0 <= currentIndices[k].1 < n
    invariant forall k :: 0 <= k < |currentIndices| ==> k == currentIndices[k].0 * n + currentIndices[k].1
    invariant forall k :: 0 <= k < |currentIndices| ==> currentIndices[k].0 < m // Add this invariant
  {
    var j := 0;
    while j < n
      invariant 0 <= j <= n
      invariant |currentIndices| == i * n + j
      invariant forall k :: 0 <= k < i * n ==> 0 <= currentIndices[k].0 < i && 0 <= currentIndices[k].1 < n
      invariant forall k :: i * n <= k < i * n + j ==> currentIndices[k].0 == i && 0 <= currentIndices[k].1 < j
      invariant forall k :: 0 <= k < |currentIndices| ==> k == currentIndices[k].0 * n + currentIndices[k].1
      invariant forall k :: 0 <= k < |currentIndices| ==> currentIndices[k].0 < m
    {
      currentIndices := currentIndices + [(i, j)];
      j := j + 1;
    }
    i := i + 1;
  }
  indices := currentIndices;
}
// </vc-code>
