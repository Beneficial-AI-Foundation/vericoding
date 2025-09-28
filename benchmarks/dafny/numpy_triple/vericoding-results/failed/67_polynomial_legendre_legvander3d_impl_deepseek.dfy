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
/* helper modified by LLM (iteration 5): Add array utility functions */
function ArrayInit2D<T>(n: int, m: int, init: T): array<array<T>> {
  var arr := new T[n][];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |arr| == n
    invariant forall j :: 0 <= j < i ==> |arr[j]| == m
  {
    arr[i] := new T[m];
    var k := 0;
    while k < m
      invariant 0 <= k <= m
      invariant |arr[i]| == m
    {
      arr[i][k] := init;
      k := k + 1;
    }
    i := i + 1;
  }
  arr
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
/* code modified by LLM (iteration 5): Fixed array initialization using 2D arrays */
{
  var n := |x|;
  var cols := (deg_x + 1) * (deg_y + 1) * (deg_z + 1);
  var arr_result := ArrayInit2D(n, cols, 0.0);
  var i := 0;
  
  while i < n
    invariant 0 <= i <= n
    invariant |arr_result| == n
    invariant forall j :: 0 <= j < n ==> |arr_result[j]| == cols
    invariant forall j :: 0 <= j < i ==> arr_result[j][0] == 1.0
  {
    arr_result[i][0] := 1.0;
    
    var p := 0;
    while p <= deg_x
      invariant 0 <= p <= deg_x + 1
    {
      var q := 0;
      while q <= deg_y
        invariant 0 <= q <= deg_y + 1
      {
        var r := 0;
        while r <= deg_z
          invariant 0 <= r <= deg_z + 1
        {
          if p != 0 || q != 0 || r != 0 {
            var col_idx := ComputeColumnIndex(p, q, r, deg_y, deg_z);
            arr_result[i][col_idx] := LegendrePolynomial(p, x[i]) * LegendrePolynomial(q, y[i]) * LegendrePolynomial(r, z[i]);
          }
          r := r + 1;
        }
        q := q + 1;
      }
      p := p + 1;
    }
    i := i + 1;
  }
  
  // Convert to seq<seq<real>>
  result := new seq<real>[n];
  var j := 0;
  while j < n
    invariant 0 <= j <= n
    invariant |result| == n
    invariant forall k :: 0 <= k < j ==> |result[k]| == cols
  {
    result[j] := arr_result[j][..];
    j := j + 1;
  }
}
// </vc-code>
