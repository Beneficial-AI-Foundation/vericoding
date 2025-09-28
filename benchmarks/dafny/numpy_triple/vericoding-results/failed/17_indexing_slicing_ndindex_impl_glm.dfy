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
function min(a: int, b: int): int { if a < b then a else b }
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
{
  var m, n := shape.0, shape.1;
  indices := [];
  for i := 0 to m
    invariant 0 <= i <= m
    invariant |indices| == i * n
    invariant forall k :: 0 <= k < |indices| ==> indices[k].0 < i && indices[k].1 < n
    invariant forall ii, jj :: 0 <= ii < i && 0 <= jj < n ==> exists k :: 0 <= k < |indices| && indices[k] == (ii, jj)
    invariant forall k :: 0 <= k < |indices| ==> k == indices[k].0 * n + indices[k].1
  {
    for j := 0 to n
      invariant 0 <= j <= n
      invariant |indices| == i * n + j
      invariant forall k :: 0 <= k < |indices| ==> (k < i * n ==> indices[k].0 < i) && (k >= i * n ==> indices[k].0 == i && indices[k].1 < j)
      invariant forall ii, jj :: (0 <= ii < i && 0 <= jj < n) || (ii == i && 0 <= jj < j) ==> exists k :: 0 <= k < |indices| && indices[k] == (ii, jj)
      invariant forall k :: 0 <= k < |indices| ==> k == indices[k].0 * n + indices[k].1
    {
      if j < n {
        indices := indices + [(i, j)];
      }
    }
  }
}
// </vc-code>
