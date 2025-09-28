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
// Helper function to convert linear index to 2D coordinates
function IndexTo2D(k: nat, shape: (nat, nat)): (nat, nat)
  requires shape.1 > 0
  requires k < shape.0 * shape.1
{
  (k / shape.1, k % shape.1)
}

// Lemma to prove the conversion is correct
lemma IndexTo2DCorrect(k: nat, shape: (nat, nat))
  requires shape.1 > 0
  requires k < shape.0 * shape.1
  ensures var (i, j) := IndexTo2D(k, shape); i * shape.1 + j == k
  ensures var (i, j) := IndexTo2D(k, shape); i < shape.0 && j < shape.1
{
  var (i, j) := IndexTo2D(k, shape);
  assert i * shape.1 + j == k by {
    assert i == k / shape.1;
    assert j == k % shape.1;
  }
}

/* helper modified by LLM (iteration 5): added lemma for coverage postcondition */
lemma AllIndicesCovered(shape: (nat, nat), indices: seq<(nat, nat)>)
  requires shape.1 > 0
  requires |indices| == shape.0 * shape.1
  requires forall idx :: 0 <= idx < |indices| ==> 
    indices[idx].0 < shape.0 && indices[idx].1 < shape.1
  requires forall idx :: 0 <= idx < |indices| ==> 
    idx == indices[idx].0 * shape.1 + indices[idx].1
  ensures forall i, j :: 0 <= i < shape.0 && 0 <= j < shape.1 ==>
    exists k :: 0 <= k < |indices| && indices[k] == (i, j)
{
  forall i, j | 0 <= i < shape.0 && 0 <= j < shape.1
    ensures exists k :: 0 <= k < |indices| && indices[k] == (i, j)
  {
    var target_k := i * shape.1 + j;
    assert 0 <= target_k < shape.0 * shape.1;
    assert 0 <= target_k < |indices|;
    assert target_k == indices[target_k].0 * shape.1 + indices[target_k].1;
    assert indices[target_k] == (i, j);
  }
}

lemma COrderUnique(i1: nat, j1: nat, i2: nat, j2: nat, shape: (nat, nat))
  requires shape.1 > 0
  requires i1 < shape.0 && j1 < shape.1
  requires i2 < shape.0 && j2 < shape.1
  requires i1 * shape.1 + j1 == i2 * shape.1 + j2
  ensures i1 == i2 && j1 == j2
{
  if i1 != i2 {
    if i1 < i2 {
      calc {
        i1 * shape.1 + j1;
        < (i1 + 1) * shape.1;  // since j1 < shape.1
        <= i2 * shape.1;      // since i1 + 1 <= i2
        <= i2 * shape.1 + j2; // since j2 >= 0
      }
      assert i1 * shape.1 + j1 < i2 * shape.1 + j2;
      assert false;
    } else {
      calc {
        i2 * shape.1 + j2;
        < (i2 + 1) * shape.1;  // since j2 < shape.1
        <= i1 * shape.1;      // since i2 + 1 <= i1
        <= i1 * shape.1 + j1; // since j1 >= 0
      }
      assert i2 * shape.1 + j2 < i1 * shape.1 + j1;
      assert false;
    }
  }
  // Now we know i1 == i2
  assert i1 == i2;
  assert i1 * shape.1 + j1 == i2 * shape.1 + j2;
  assert j1 == j2;
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
  /* code modified by LLM (iteration 5): added proof for coverage postcondition */
  if shape.0 == 0 || shape.1 == 0 {
    indices := [];
    return;
  }
  
  indices := [];
  var k := 0;
  
  while k < shape.0 * shape.1
    invariant 0 <= k <= shape.0 * shape.1
    invariant |indices| == k
    invariant forall idx :: 0 <= idx < |indices| ==> 
      indices[idx].0 < shape.0 && indices[idx].1 < shape.1
    invariant forall idx :: 0 <= idx < |indices| ==> 
      idx == indices[idx].0 * shape.1 + indices[idx].1
    invariant shape.1 > 0
    invariant forall i, j :: 0 <= i < shape.0 && 0 <= j < shape.1 && i * shape.1 + j < k ==>
      indices[i * shape.1 + j] == (i, j)
  {
    var coords := IndexTo2D(k, shape);
    IndexTo2DCorrect(k, shape);
    indices := indices + [coords];
    k := k + 1;
  }
  
  AllIndicesCovered(shape, indices);
}
// </vc-code>
