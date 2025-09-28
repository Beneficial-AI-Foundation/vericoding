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

// Helper function to compute the total number of indices
function TotalIndices(shape: (nat, nat)): nat
{
  shape.0 * shape.1
}

// Helper predicate to check if an index is within bounds
predicate ValidIndex(shape: (nat, nat), index: (nat, nat))
{
  0 <= index.0 < shape.0 && 0 <= index.1 < shape.1
}

// Helper lemma to prove that all indices are generated
/* helper modified by LLM (iteration 4): Fixed quantifier with proper triggers */
lemma AllIndicesGenerated(shape: (nat, nat), indices: seq<(nat, nat)>)
  requires |indices| == shape.0 * shape.1
  requires forall k :: 0 <= k < |indices| ==> ValidIndex(shape, indices[k]) && k == indices[k].0 * shape.1 + indices[k].1
  ensures forall i, j :: 0 <= i < shape.0 && 0 <= j < shape.1 ==>
    exists k :: 0 <= k < |indices| && indices[k] == (i, j)
{
  if shape.0 > 0 && shape.1 > 0 {
    forall i, j | 0 <= i < shape.0 && 0 <= j < shape.1
      ensures exists k :: 0 <= k < |indices| && indices[k] == (i, j)
    {
      var k := i * shape.1 + j;
      assert 0 <= k < |indices| by {
        calc {
          i * shape.1 + j;
          < shape.0 * shape.1;
          == |indices|;
        }
      };
      assert indices[k] == (i, j) by {
        assert k == indices[k].0 * shape.1 + indices[k].1;
      };
    }
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
  /* code modified by LLM (iteration 4): Fixed loop invariants and assertions */
  var m := shape.0;
  var n := shape.1;
  indices := [];
  
  var i := 0;
  while i < m
    invariant 0 <= i <= m
    invariant |indices| == i * n
    invariant forall k :: 0 <= k < |indices| ==> 
      indices[k].0 < i && indices[k].1 < n && k == indices[k].0 * n + indices[k].1
    invariant forall ii, jj :: 0 <= ii < i && 0 <= jj < n ==> exists k :: 0 <= k < |indices| && indices[k] == (ii, jj)
  {
    var j := 0;
    while j < n
      invariant 0 <= j <= n
      invariant |indices| == i * n + j
      invariant forall k :: 0 <= k < |indices| ==> 
        indices[k].0 <= i && indices[k].1 < n && k == indices[k].0 * n + indices[k].1
      invariant forall idx :: 0 <= idx < j ==> indices[i * n + idx] == (i, idx)
    {
      indices := indices + [(i, j)];
      j := j + 1;
    }
    i := i + 1;
  }
  
  // Call the helper lemma to prove the ensures clause
  AllIndicesGenerated(shape, indices);
}
// </vc-code>
