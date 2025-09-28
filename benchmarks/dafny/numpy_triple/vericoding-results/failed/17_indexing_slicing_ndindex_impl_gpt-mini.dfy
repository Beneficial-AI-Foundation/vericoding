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
/* helper modified by LLM (iteration 3): if product of nats > 0 then both factors > 0 */
lemma ProdPositiveImpliesFactorsPositive(a: nat, b: nat)
  requires a * b > 0
  ensures a > 0 && b > 0
{
  if a == 0 {
    assert a * b == 0;
    assert false;
  }
  if b == 0 {
    assert a * b == 0;
    assert false;
  }
}

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
  /* code modified by LLM (iteration 3): build indices by single loop over k, using division and modulo and a helper lemma to ensure n>0 when needed */
  var m := shape.0;
  var n := shape.1;
  var total := m * n;
  indices := [];
  var k: nat := 0;
  while k < total
    invariant 0 <= k <= total
    invariant |indices| == k
    invariant forall t :: 0 <= t < k ==> indices[t].0 < m && indices[t].1 < n
    invariant forall t :: 0 <= t < k ==> t == indices[t].0 * n + indices[t].1
  {
    assert total > 0;
    ProdPositiveImpliesFactorsPositive(m, n);
    assert n > 0;
    var i := k / n;
    var j := k % n;
    indices := indices + [(i, j)];
    k := k + 1;
  }
}

// </vc-code>
