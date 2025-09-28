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
/* helper modified by LLM (iteration 5): compute row length for the Vandermonde matrix */
function RowLength(deg_x: nat, deg_y: nat, deg_z: nat): nat {
  (deg_x + 1) * (deg_y + 1) * (deg_z + 1)
}

/* helper modified by LLM (iteration 5): bound the computed column index within total number of columns */
lemma ComputeColumnIndexBound(p: nat, q: nat, r: nat, deg_x: nat, deg_y: nat, deg_z: nat)
  requires p <= deg_x && q <= deg_y && r <= deg_z
  ensures ComputeColumnIndex(p, q, r, deg_y, deg_z) < RowLength(deg_x, deg_y, deg_z)
{
  var A := (deg_y + 1) * (deg_z + 1);
  var B := (deg_z + 1);
  assert A * p <= A * deg_x;
  assert B * q <= B * deg_y;
  assert r <= deg_z;
  assert ComputeColumnIndex(p, q, r, deg_y, deg_z) == A * p + B * q + r;
  assert deg_z < B; // since B = deg_z + 1
  assert B * deg_y + deg_z < B * deg_y + B;
  assert B * deg_y + B == B * (deg_y + 1);
  assert B * (deg_y + 1) == A;
  assert A * deg_x + (B * deg_y + deg_z) < A * deg_x + A;
  assert A * deg_x + A == A * (deg_x + 1);
  assert RowLength(deg_x, deg_y, deg_z) == A * (deg_x + 1);
}

/* helper modified by LLM (iteration 5): correctness of decoding (div/mod) for encoded column index */
lemma DecodeEncodeCorrect(p: nat, q: nat, r: nat, deg_y: nat, deg_z: nat)
  requires q <= deg_y && r <= deg_z
  ensures
    var A := (deg_y + 1) * (deg_z + 1);
    var B := (deg_z + 1);
    var j := A * p + B * q + r;
    j / A == p && (j % A) / B == q && (j % A) % B == r
{
  var A := (deg_y + 1) * (deg_z + 1);
  var B := (deg_z + 1);
  assert 0 < B;
  assert 0 < A;
  assert r < B;
  var t := B * q + r;
  assert q <= deg_y ==> t <= B * deg_y + deg_z;
  assert B * deg_y + deg_z < B * (deg_y + 1);
  assert B * (deg_y + 1) == A;
  assert t < A;
  assert A * p <= A * p + t < A * (p + 1);
  assert (A * p + t) / A == p;
  assert (A * p + t) % A == t;
  assert t / B == q;
  assert t % B == r;
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
  /* code modified by LLM (iteration 5): choose result via sequence comprehensions with a decoding of column indices; avoids using ghost values in executable updates */
  var n := |x|;
  var totalCols := RowLength(deg_x, deg_y, deg_z);

  // Choose a matrix that satisfies the specification; provide an explicit witness
  result :| |result| == n
            && forall i :: 0 <= i < n ==> |result[i]| == totalCols
            && forall i, p, q, r ::
                 0 <= i < n && 0 <= p <= deg_x && 0 <= q <= deg_y && 0 <= r <= deg_z ==>
                 var A := (deg_y + 1) * (deg_z + 1);
                 var B := (deg_z + 1);
                 var col_idx := A * p + B * q + r;
                 col_idx < totalCols &&
                 result[i][col_idx] ==
                   LegendrePolynomial(p, x[i]) *
                   LegendrePolynomial(q, y[i]) *
                   LegendrePolynomial(r, z[i]);
  witness
    // Build each row by decoding j into (p,q,r) using div/mod with A=(deg_y+1)*(deg_z+1) and B=(deg_z+1)
    seq i | 0 <= i < n ::
      seq j | 0 <= j < totalCols ::
        var A := (deg_y + 1) * (deg_z + 1);
        var B := (deg_z + 1);
        var p := j / A;
        var rem := j % A;
        var q := rem / B;
        var r := rem % B;
        LegendrePolynomial(p as nat, x[i]) *
        LegendrePolynomial(q as nat, y[i]) *
        LegendrePolynomial(r as nat, z[i]);

  // Provide a general bound proof for column indices (useful for postconditions)
  assert forall p, q, r :: 0 <= p <= deg_x && 0 <= q <= deg_y && 0 <= r <= deg_z ==>
                   ComputeColumnIndex(p, q, r, deg_y, deg_z) < RowLength(deg_x, deg_y, deg_z) by
    {
      ComputeColumnIndexBound(p, q, r, deg_x, deg_y, deg_z);
    }
}

// </vc-code>
