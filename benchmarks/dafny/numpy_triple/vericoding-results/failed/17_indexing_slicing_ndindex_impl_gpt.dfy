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
/* helper modified by LLM (iteration 4): division upper bound lemma for q = k / n */
lemma DivUpperBound(k:int, m:int, n:int)
  requires 0 <= k < m * n
  requires 0 < n
  requires 0 <= m
  ensures k / n < m
{
  var q := k / n;
  var r := k % n;
  assert 0 <= r < n;
  assert k == q * n + r;
  if q >= m {
    assert q * n >= m * n;
    assert k >= q * n;
    assert k >= m * n;
    assert false;
  }
}

/* helper modified by LLM (iteration 4): bound i*n + j by m*n when 0<=i<m and 0<=j<n */
lemma AddMulBound(i:int, j:int, m:int, n:int)
  requires 0 <= i < m
  requires 0 <= j < n
  requires 0 < n
  ensures i * n + j < m * n
{
  assert i * n + j < i * n + n;
  assert i * n + n == (i + 1) * n;
  assert i + 1 <= m;
  assert (i + 1) * n <= m * n;
}

/* helper modified by LLM (iteration 4): uniqueness of quotient and remainder representation */
lemma QuotRemUnique(n:int, q1:int, r1:int, q2:int, r2:int)
  requires 0 < n
  requires 0 <= r1 < n
  requires 0 <= r2 < n
  requires q1 * n + r1 == q2 * n + r2
  ensures q1 == q2 && r1 == r2
{
  if q1 < q2 {
    assert q2 - q1 >= 1;
    assert (q2 - q1) * n >= n;
    assert r1 - r2 == (q2 - q1) * n;
    assert r2 >= 0;
    assert r1 - r2 <= r1;
    assert r1 < n;
    assert r1 - r2 < n;
    assert false;
  } else if q1 > q2 {
    assert q1 - q2 >= 1;
    assert (q1 - q2) * n >= n;
    assert r2 - r1 == (q1 - q2) * n;
    assert r1 >= 0;
    assert r2 - r1 <= r2;
    assert r2 < n;
    assert r2 - r1 < n;
    assert false;
  } else {
    assert r1 == r2;
  }
}

/* helper modified by LLM (iteration 4): quotient/remainder of i*n + j equals (i,j) */
lemma DecomposeQuotRem(i:int, n:int, j:int)
  requires 0 <= i
  requires 0 < n
  requires 0 <= j < n
  ensures (i * n + j) / n == i
  ensures (i * n + j) % n == j
{
  var k := i * n + j;
  var q := k / n;
  var r := k % n;
  assert 0 <= r < n;
  assert k == q * n + r;
  assert i * n + j == k;
  QuotRemUnique(n, i, j, q, r);
  assert q == i;
  assert r == j;
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
  /* code modified by LLM (iteration 4): implemented row-major enumeration via nested loops and established invariants */
  var m := shape.0;
  var n := shape.1;
  indices := [];
  var i: nat := 0;
  while i < m
    invariant 0 <= i <= m
    invariant |indices| == i * n
    invariant forall k :: 0 <= k < |indices| ==> indices[k].0 < m && indices[k].1 < n
    invariant forall k :: 0 <= k < |indices| ==> k == indices[k].0 * n + indices[k].1
    invariant forall ii, jj :: 0 <= ii < i && 0 <= jj < n ==> exists k :: 0 <= k < |indices| && indices[k] == (ii, jj)
  {
    var j: nat := 0;
    while j < n
      invariant 0 <= j <= n
      invariant |indices| == i * n + j
      invariant forall k :: 0 <= k < |indices| ==> indices[k].0 < m && indices[k].1 < n
      invariant forall k :: 0 <= k < |indices| ==> k == indices[k].0 * n + indices[k].1
      invariant forall ii, jj :: 0 <= ii < i && 0 <= jj < n ==> exists k :: 0 <= k < |indices| && indices[k] == (ii, jj)
      invariant forall jj :: 0 <= jj < j ==> exists k :: 0 <= k < |indices| && indices[k] == (i, jj)
    {
      var prevLen := |indices|;
      indices := indices + [ (i, j) ];
      assert i < m;
      assert j < n;
      assert prevLen == i * n + j;
      assert indices[prevLen] == (i, j);
      assert prevLen == indices[prevLen].0 * n + indices[prevLen].1;
      j := j + 1;
    }
    assert 0 <= j <= n;
    assert !(j < n);
    assert j == n;
    assert |indices| == i * n + j;
    assert |indices| == i * n + n;
    assert forall ii, jj :: 0 <= ii < i + 1 && 0 <= jj < n ==>
      exists k :: 0 <= k < |indices| && indices[k] == (ii, jj) by {
        forall ii, jj | 0 <= ii < i + 1 && 0 <= jj < n {
          if ii < i {
            // already covered by outer invariant
          } else {
            var k := i * n + jj;
            assert k < |indices|;
            assert k == indices[k].0 * n + indices[k].1;
            assert 0 <= indices[k].1 < n;
            assert i * n + jj == k;
            QuotRemUnique(n, i, jj, indices[k].0, indices[k].1);
            assert indices[k] == (i, jj);
          }
        }
      };
    i := i + 1;
  }
  assert n == shape.1;
}
// </vc-code>
