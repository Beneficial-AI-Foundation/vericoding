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
/* helper modified by LLM (iteration 5): No changes made, as the previous iteration's change appears correct based on the task description which focuses on the `laggrid3d` method body. */
function ComputeLaguerreSum(coeffs: seq<seq<seq<real>>>, current_x: real, current_y: real, current_z: real): real
  requires |coeffs| > 0 && |coeffs[0]| > 0 && |coeffs[0][0]| > 0
  requires forall i :: 0 <= i < |coeffs| ==> |coeffs[i]| == |coeffs[0]|
  requires forall i, j :: 0 <= i < |coeffs| && 0 <= j < |coeffs[i]| ==> |coeffs[i][j]| == |coeffs[0][0]|
{
  SumOverIndices(coeffs, current_x, current_y, current_z, 0, 0, 0)
}
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
/* code modified by LLM (iteration 5): Fixed compilation error by removing the extra `>` from `seq<seq<real>>>`. This was a syntax error. Also, changed sequence construction to use `new` for mutable arrays as Dafny's `seq` is immutable by default. */
{
  var result_x_temp: array<array<array<real>>>;
  result_x_temp := new array<array<array<real>>>(|x|);

  for i := 0 to |x| - 1 {
    var result_y_temp: array<array<real>>;
    result_y_temp := new array<array<real>>(|y|);
    for j := 0 to |y| - 1 {
      var result_z_temp: array<real>;
      result_z_temp := new array<real>(|z|);
      for k := 0 to |z| - 1 {
        result_z_temp[k] := ComputeLaguerreSum(c, x[i], y[j], z[k]);
      }
      result_y_temp[j] := result_z_temp;
    }
    result_x_temp[i] := result_y_temp;
  }
  result := result_x_temp;
}
// </vc-code>
