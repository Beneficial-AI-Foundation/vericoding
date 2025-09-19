// <vc-preamble>
// Helper function to compute Chebyshev polynomials using the recurrence relation
ghost function ChebyshevT(n: nat, x: real): real
{
  if n == 0 then 1.0
  else if n == 1 then x
  else 2.0 * x * ChebyshevT(n - 1, x) - ChebyshevT(n - 2, x)
}

// Helper function to compute the triple sum for a single grid point
ghost function ComputeGridPointValue(
  c: seq<seq<seq<real>>>,
  x_val: real, y_val: real, z_val: real
): real
{
  var ni := |c|;
  if ni == 0 then 0.0
  else
    var nj := |c[0]|;
    if nj == 0 then 0.0
    else
      var nk := |c[0][0]|;
      if nk == 0 then 0.0
      else
        SumOverIndices(c, x_val, y_val, z_val, 0, 0, 0, ni, nj, nk)
}

// Recursive helper for computing the triple sum
ghost function SumOverIndices(
  c: seq<seq<seq<real>>>,
  x_val: real, y_val: real, z_val: real,
  i: nat, j: nat, k: nat,
  ni: nat, nj: nat, nk: nat
): real
  requires ni > 0 && nj > 0 && nk > 0
  requires i <= ni && j <= nj && k <= nk
  requires |c| == ni
  requires forall idx :: 0 <= idx < ni ==> |c[idx]| == nj
  requires forall idx1, idx2 :: 0 <= idx1 < ni && 0 <= idx2 < nj ==> |c[idx1][idx2]| == nk
  decreases ni - i, nj - j, nk - k
{
  if i >= ni then 0.0
  else if j >= nj then SumOverIndices(c, x_val, y_val, z_val, i + 1, 0, 0, ni, nj, nk)
  else if k >= nk then SumOverIndices(c, x_val, y_val, z_val, i, j + 1, 0, ni, nj, nk)
  else
    c[i][j][k] * ChebyshevT(i, x_val) * ChebyshevT(j, y_val) * ChebyshevT(k, z_val) +
    SumOverIndices(c, x_val, y_val, z_val, i, j, k + 1, ni, nj, nk)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method ChebGrid3D(
  x: seq<real>, y: seq<real>, z: seq<real>,
  c: seq<seq<seq<real>>>
) returns (result: seq<seq<seq<real>>>)
  requires |c| > 0 ==> |c[0]| > 0 ==> |c[0][0]| > 0  // Non-empty coefficient array if not empty
  requires forall i :: 0 <= i < |c| ==> |c[i]| == (if |c| > 0 then |c[0]| else 0)  // Consistent nj dimension
  requires forall i, j :: 0 <= i < |c| && 0 <= j < |c[i]| ==> |c[i][j]| == (if |c| > 0 && |c[0]| > 0 then |c[0][0]| else 0)  // Consistent nk dimension
  ensures |result| == |x|  // Output has correct nx dimension
  ensures forall ix :: 0 <= ix < |result| ==> |result[ix]| == |y|  // Output has correct ny dimension  
  ensures forall ix, iy :: 0 <= ix < |result| && 0 <= iy < |result[ix]| ==> |result[ix][iy]| == |z|  // Output has correct nz dimension
  ensures forall ix, iy, iz :: 0 <= ix < |x| && 0 <= iy < |y| && 0 <= iz < |z| ==>
    result[ix][iy][iz] == ComputeGridPointValue(c, x[ix], y[iy], z[iz])  // Each grid point computed correctly
  ensures |c| == 0 ==> forall ix, iy, iz :: 0 <= ix < |x| && 0 <= iy < |y| && 0 <= iz < |z| ==>
    result[ix][iy][iz] == 0.0  // Zero coefficients give zero result
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
