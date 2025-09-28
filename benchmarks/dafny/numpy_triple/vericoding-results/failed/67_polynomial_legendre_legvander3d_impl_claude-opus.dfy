// <vc-preamble>
/*
 * 3D Pseudo-Vandermonde matrix construction for Legendre polynomials.
 * 
 * This module provides functionality to construct a pseudo-Vandermonde matrix
 * for 3D Legendre polynomials given sample points and polynomial degrees.
 * The matrix entries follow the pattern V[i, col] = L_p(x[i]) * L_q(y[i]) * L_r(z[i])
 * where L_k represents the k-th Legendre polynomial.
 */

// Ghost function representing the evaluation of the k-th Legendre polynomial at point x
ghost function LegendrePolynomial(k: nat, x: real): real

// Ghost function to compute the column index for given polynomial degrees
ghost function ComputeColumnIndex(p: nat, q: nat, r: nat, deg_y: nat, deg_z: nat): nat
{
  (deg_y + 1) * (deg_z + 1) * p + (deg_z + 1) * q + r
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added decreases clause for termination and removed axiom bypass */
function EvalLegendre(k: nat, x: real): real
  decreases k
  ensures k == 0 ==> EvalLegendre(k, x) == 1.0
{
  if k == 0 then 1.0
  else if k == 1 then x
  else ((2.0 * (k as real) - 1.0) * x * EvalLegendre(k - 1, x) - ((k as real) - 1.0) * EvalLegendre(k - 2, x)) / (k as real)
}
// </vc-helpers>

// <vc-spec>
method legvander3d(x: seq<real>, y: seq<real>, z: seq<real>, deg_x: nat, deg_y: nat, deg_z: nat)
  returns (result: seq<seq<real>>)
  // Input vectors must have the same length
  requires |x| == |y| == |z|
  
  // Result matrix has correct outer dimension (number of sample points)
  ensures |result| == |x|
  
  // Each row has correct inner dimension (number of polynomial combinations)
  ensures forall i :: 0 <= i < |result| ==> |result[i]| == (deg_x + 1) * (deg_y + 1) * (deg_z + 1)
  
  // First column corresponds to L_0(x) * L_0(y) * L_0(z) = 1 * 1 * 1 = 1
  ensures forall i :: 0 <= i < |result| ==> result[i][0] == 1.0
  
  // Each matrix entry is the product of appropriate Legendre polynomial evaluations
  ensures forall i, p, q, r :: 
    0 <= i < |result| && 0 <= p <= deg_x && 0 <= q <= deg_y && 0 <= r <= deg_z ==>
    var col_idx := ComputeColumnIndex(p, q, r, deg_y, deg_z);
    col_idx < (deg_x + 1) * (deg_y + 1) * (deg_z + 1) &&
    result[i][col_idx] == LegendrePolynomial(p, x[i]) * LegendrePolynomial(q, y[i]) * LegendrePolynomial(r, z[i])
    
  // Column indices are computed correctly and within bounds
  ensures forall p, q, r :: 
    0 <= p <= deg_x && 0 <= q <= deg_y && 0 <= r <= deg_z ==>
    ComputeColumnIndex(p, q, r, deg_y, deg_z) < (deg_x + 1) * (deg_y + 1) * (deg_z + 1)
    
  // L_0 polynomial evaluates to 1 (fundamental property of Legendre polynomials)
  ensures forall x :: LegendrePolynomial(0, x) == 1.0
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Removed all axiom bypasses and fixed invariant structure */
  var n := |x|;
  var num_cols := (deg_x + 1) * (deg_y + 1) * (deg_z + 1);
  result := [];
  
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> |result[k]| == num_cols
    invariant forall k :: 0 <= k < i ==> result[k][0] == 1.0
    invariant forall k, p, q, r :: 
      0 <= k < i && 0 <= p <= deg_x && 0 <= q <= deg_y && 0 <= r <= deg_z ==>
      var col_idx := ComputeColumnIndex(p, q, r, deg_y, deg_z);
      col_idx < num_cols &&
      result[k][col_idx] == EvalLegendre(p, x[k]) * EvalLegendre(q, y[k]) * EvalLegendre(r, z[k])
  {
    var row := [];
    var p := 0;
    
    while p <= deg_x
      invariant 0 <= p <= deg_x + 1
      invariant |row| == p * (deg_y + 1) * (deg_z + 1)
      invariant p > 0 ==> row[0] == 1.0
      invariant forall p', q', r' ::
        0 <= p' < p && 0 <= q' <= deg_y && 0 <= r' <= deg_z ==>
        var col_idx := ComputeColumnIndex(p', q', r', deg_y, deg_z);
        col_idx < |row| &&
        row[col_idx] == EvalLegendre(p', x[i]) * EvalLegendre(q', y[i]) * EvalLegendre(r', z[i])
    {
      var q := 0;
      
      while q <= deg_y
        invariant 0 <= q <= deg_y + 1
        invariant |row| == p * (deg_y + 1) * (deg_z + 1) + q * (deg_z + 1)
        invariant p > 0 || q > 0 ==> row[0] == 1.0
        invariant forall p', q', r' ::
          0 <= p' < p && 0 <= q' <= deg_y && 0 <= r' <= deg_z ==>
          var col_idx := ComputeColumnIndex(p', q', r', deg_y, deg_z);
          col_idx < |row| &&
          row[col_idx] == EvalLegendre(p', x[i]) * EvalLegendre(q', y[i]) * EvalLegendre(r', z[i])
        invariant forall q', r' ::
          p == p && 0 <= q' < q && 0 <= r' <= deg_z ==>
          var col_idx := ComputeColumnIndex(p, q', r', deg_y, deg_z);
          col_idx < |row| &&
          row[col_idx] == EvalLegendre(p, x[i]) * EvalLegendre(q', y[i]) * EvalLegendre(r', z[i])
      {
        var r := 0;
        
        while r <= deg_z
          invariant 0 <= r <= deg_z + 1
          invariant |row| == p * (deg_y + 1) * (deg_z + 1) + q * (deg_z + 1) + r
          invariant p > 0 || q > 0 || r > 0 ==> row[0] == 1.0
          invariant forall p', q', r' ::
            0 <= p' < p && 0 <= q' <= deg_y && 0 <= r' <= deg_z ==>
            var col_idx := ComputeColumnIndex(p', q', r', deg_y, deg_z);
            col_idx < |row| &&
            row[col_idx] == EvalLegendre(p', x[i]) * EvalLegendre(q', y[i]) * EvalLegendre(r', z[i])
          invariant forall q', r' ::
            p == p && 0 <= q' < q && 0 <= r' <= deg_z ==>
            var col_idx := ComputeColumnIndex(p, q', r', deg_y, deg_z);
            col_idx < |row| &&
            row[col_idx] == EvalLegendre(p, x[i]) * EvalLegendre(q', y[i]) * EvalLegendre(r', z[i])
          invariant forall r' ::
            p == p && q == q && 0 <= r' < r ==>
            var col_idx := ComputeColumnIndex(p, q, r', deg_y, deg_z);
            col_idx < |row| &&
            row[col_idx] == EvalLegendre(p, x[i]) * EvalLegendre(q, y[i]) * EvalLegendre(r', z[i])
        {
          var val := EvalLegendre(p, x[i]) * EvalLegendre(q, y[i]) * EvalLegendre(r, z[i]);
          row := row + [val];
          r := r + 1;
        }
        q := q + 1;
      }
      p := p + 1;
    }
    
    result := result + [row];
    i := i + 1;
  }
}
// </vc-code>
