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
function C_order_index(k: nat, n: nat): (nat, nat)
  requires n > 0
{
  (k / n, k % n)
}

/* helper modified by LLM (iteration 5): [fixed let-binding syntax in ensures clause from '=' to ':='] */
lemma C_order_bijection(m: nat, n: nat)
  requires n > 0
  // Surjectivity: every pair (i, j) is generated from some k.
  ensures forall i, j :: 0 <= i < m && 0 <= j < n ==>
    exists k :: 0 <= k < m * n && C_order_index(k, n) == (i, j)
  // Properties of the mapping from k to (i, j).
  ensures forall k :: 0 <= k < m * n ==>
    let (i, j) := C_order_index(k, n) in
    // The generated index (i, j) is within bounds.
    i < m && j < n &&
    // The C-order formula k = i*n + j holds.
    k == i * n + j
{
  // The body is empty as Dafny's SMT solver can prove the ensures clauses
  // from the properties of integer division and modulo.
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
  /* code modified by LLM (iteration 5): [retaining logic which depends on fixed helper] */
  var m := shape.0;
  var n := shape.1;
  if n == 0 {
    // If the second dimension is 0, the total number of elements is 0.
    // The result is an empty sequence.
    indices := [];
  } else {
    // For the main case, we call the lemma to establish the needed properties.
    C_order_bijection(m, n);
    // Then, we construct the sequence of indices. The postconditions of this method
    // follow directly from the postconditions of the C_order_bijection lemma.
    indices := seq(m * n, k => C_order_index(k, n));
  }
}
// </vc-code>
