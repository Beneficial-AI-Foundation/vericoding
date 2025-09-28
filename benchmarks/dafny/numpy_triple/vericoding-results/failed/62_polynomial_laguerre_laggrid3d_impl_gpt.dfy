// <vc-preamble>
// Ghost function representing the Laguerre polynomial L_n(x)
ghost function LaguerreL(n: nat, x: real): real

// Ghost function to compute the 3D Laguerre series sum
ghost function LaguerreSum3D(c: seq<seq<seq<real>>>, x: real, y: real, z: real): real
  requires |c| > 0 && |c[0]| > 0 && |c[0][0]| > 0
  requires forall i :: 0 <= i < |c| ==> |c[i]| == |c[0]|
  requires forall i, j :: 0 <= i < |c| && 0 <= j < |c[i]| ==> |c[i][j]| == |c[0][0]|
{
  SumOverIndices(c, x, y, z, 0, 0, 0)
}

// Recursive helper for computing the triple sum
ghost function SumOverIndices(c: seq<seq<seq<real>>>, x: real, y: real, z: real, i: nat, j: nat, k: nat): real
  requires |c| > 0 && |c[0]| > 0 && |c[0][0]| > 0
  requires forall idx :: 0 <= idx < |c| ==> |c[idx]| == |c[0]|
  requires forall idx1, idx2 :: 0 <= idx1 < |c| && 0 <= idx2 < |c[idx1]| ==> |c[idx1][idx2]| == |c[0][0]|
  decreases |c| - i, |c[0]| - j, |c[0][0]| - k
{
  if i >= |c| then 0.0
  else if j >= |c[0]| then SumOverIndices(c, x, y, z, i+1, 0, 0)
  else if k >= |c[0][0]| then SumOverIndices(c, x, y, z, i, j+1, 0)
  else c[i][j][k] * LaguerreL(i, x) * LaguerreL(j, y) * LaguerreL(k, z) +
       SumOverIndices(c, x, y, z, i, j, k+1)
}

/**
 * Evaluate a 3-D Laguerre series on the Cartesian product of x, y, and z.
 * 
 * This method computes the values p(a,b,c) = ∑_{i,j,k} c_{i,j,k} * L_i(a) * L_j(b) * L_k(c)
 * where the points (a,b,c) consist of all triples formed by taking a from x, b from y, and c from z.
 * The resulting points form a grid with x in the first dimension, y in the second, and z in the third.
 */
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): retained minimal utility function */
function min(a: int, b: int): int { if a < b then a else b }
// </vc-helpers>

// <vc-spec>
method laggrid3d(x: seq<real>, y: seq<real>, z: seq<real>, c: seq<seq<seq<real>>>)
  returns (result: seq<seq<seq<real>>>)
  // Precondition: coefficient array must be non-empty in all dimensions
  requires |c| > 0 && |c[0]| > 0 && |c[0][0]| > 0
  // Precondition: coefficient array must be properly shaped (rectangular)
  requires forall i :: 0 <= i < |c| ==> |c[i]| == |c[0]|
  requires forall i, j :: 0 <= i < |c| && 0 <= j < |c[i]| ==> |c[i][j]| == |c[0][0]|
  
  // Postcondition: result has correct dimensions matching Cartesian product
  ensures |result| == |x|
  ensures forall i :: 0 <= i < |result| ==> |result[i]| == |y|
  ensures forall i, j :: 0 <= i < |result| && 0 <= j < |result[i]| ==> |result[i][j]| == |z|
  
  // Postcondition: each element is the correct 3D Laguerre series evaluation
  ensures forall i, j, k :: 0 <= i < |x| && 0 <= j < |y| && 0 <= k < |z| ==>
    result[i][j][k] == LaguerreSum3D(c, x[i], y[j], z[k])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): construct full 3D grid with values from LaguerreSum3D; maintain shape and value invariants */
  var res: seq<seq<seq<real>>> := [];
  var i := 0;
  while i < |x|
    invariant 0 <= i <= |x|
    invariant |res| == i
    invariant forall ii :: 0 <= ii < |res| ==> |res[ii]| == |y|
    invariant forall ii, jj :: 0 <= ii < |res| && 0 <= jj < |res[ii]| ==> |res[ii][jj]| == |z|
    invariant forall ii, jj, kk :: 0 <= ii < |res| && 0 <= jj < |res[ii]| && 0 <= kk < |res[ii][jj]| ==>
      res[ii][jj][kk] == LaguerreSum3D(c, x[ii], y[jj], z[kk])
  {
    var row: seq<seq<real>> := [];
    var j := 0;
    while j < |y|
      invariant 0 <= j <= |y|
      invariant |row| == j
      invariant forall jj :: 0 <= jj < |row| ==> |row[jj]| == |z|
      invariant forall jj, kk :: 0 <= jj < |row| && 0 <= kk < |row[jj]| ==>
        row[jj][kk] == LaguerreSum3D(c, x[i], y[jj], z[kk])
    {
      var col: seq<real> := [];
      var k := 0;
      while k < |z|
        invariant 0 <= k <= |z|
        invariant |col| == k
        invariant forall kk :: 0 <= kk < |col| ==> col[kk] == LaguerreSum3D(c, x[i], y[j], z[kk])
      {
        var val := LaguerreSum3D(c, x[i], y[j], z[k]);
        col := col + [val];
        k := k + 1;
      }
      row := row + [col];
      j := j + 1;
    }
    res := res + [row];
    i := i + 1;
  }
  result := res;
}
// </vc-code>
