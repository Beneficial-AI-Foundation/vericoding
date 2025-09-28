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
/* helper modified by LLM (iteration 5): ghost LegendrePolynomial definition */
ghost function LegendrePolynomial(k: nat, x: real): real
  decreases k
{
  if k == 0 then 1.0
  else if k == 1 then x
  else ((2.0 * (k as real) - 1.0) * x * LegendrePolynomial(k - 1, x) - ((k as real) - 1.0) * LegendrePolynomial(k - 2, x)) / (k as real)
}

/* helper modified by LLM (iteration 5): executable Legendre polynomial (recurrence) */
function LegendrePolynomialExec(k: nat, x: real): real
  decreases k
{
  if k == 0 then 1.0
  else if k == 1 then x
  else ((2.0 * (k as real) - 1.0) * x * LegendrePolynomialExec(k - 1, x) - ((k as real) - 1.0) * LegendrePolynomialExec(k - 2, x)) / (k as real)
}

/* helper modified by LLM (iteration 5): relate ghost LegendrePolynomial to executable LegendrePolynomialExec */
lemma LegendrePolynomial_Equals_Exec(k: nat, x: real)
  decreases k
  ensures LegendrePolynomial(k, x) == LegendrePolynomialExec(k, x)
{
  if k == 0 {
    // both sides evaluate to 1.0 by definition
  } else if k == 1 {
    // both sides evaluate to x by definition
  } else {
    // inductive hypotheses
    LegendrePolynomial_Equals_Exec(k - 1, x);
    LegendrePolynomial_Equals_Exec(k - 2, x);
    // expand definitions to show equality
    assert LegendrePolynomial(k, x) == ((2.0 * (k as real) - 1.0) * x * LegendrePolynomial(k - 1, x) - ((k as real) - 1.0) * LegendrePolynomial(k - 2, x)) / (k as real);
    assert LegendrePolynomialExec(k, x) == ((2.0 * (k as real) - 1.0) * x * LegendrePolynomialExec(k - 1, x) - ((k as real) - 1.0) * LegendrePolynomialExec(k - 2, x)) / (k as real);
    assert LegendrePolynomial(k - 1, x) == LegendrePolynomialExec(k - 1, x);
    assert LegendrePolynomial(k - 2, x) == LegendrePolynomialExec(k - 2, x);
  }
}

/* helper modified by LLM (iteration 5): Prove column index is within bounds */
lemma ColumnIndexWithinBounds(p: nat, q: nat, r: nat, deg_x: nat, deg_y: nat, deg_z: nat)
  requires p <= deg_x && q <= deg_y && r <= deg_z
  ensures ComputeColumnIndex(p, q, r, deg_y, deg_z) < (deg_x + 1) * (deg_y + 1) * (deg_z + 1)
{
  var block := (deg_y + 1) * (deg_z + 1);
  assert ComputeColumnIndex(p, q, r, deg_y, deg_z) == block * p + (deg_z + 1) * q + r;
  var max := block * p + (deg_z + 1) * deg_y + deg_z;
  assert (deg_z + 1) * q + r <= (deg_z + 1) * deg_y + deg_z;
  assert ComputeColumnIndex(p, q, r, deg_y, deg_z) <= max;
  assert max == block * (p + 1) - 1;
  assert p + 1 <= deg_x + 1;
  assert max <= block * (deg_x + 1) - 1;
  assert max < block * (deg_x + 1);
  assert max < (deg_x + 1) * (deg_y + 1) * (deg_z + 1);
  assert ComputeColumnIndex(p, q, r, deg_y, deg_z) < (deg_x + 1) * (deg_y + 1) * (deg_z + 1);
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
  /* code modified by LLM (iteration 5): build matrix rows using executable LegendrePolynomialExec evaluations */
  var n := |x|;
  var cols := (deg_x + 1) * (deg_y + 1) * (deg_z + 1);
  result := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |result| == i
    invariant forall ii :: 0 <= ii < i ==> |result[ii]| == cols
  {
    var row := [];
    var j := 0;
    var block := (deg_y + 1) * (deg_z + 1);
    while j < cols
      invariant 0 <= j <= cols
      invariant |row| == j
      invariant forall jj :: 0 <= jj < j ==>
        var pp := jj / block;
        var rem := jj % block;
        var qq := rem / (deg_z + 1);
        var rr := rem % (deg_z + 1);
        row[jj] == LegendrePolynomialExec(pp, x[i]) * LegendrePolynomialExec(qq, y[i]) * LegendrePolynomialExec(rr, z[i])
    {
      var p := j / block;
      var rem := j % block;
      var q := rem / (deg_z + 1);
      var r := rem % (deg_z + 1);
      assert p <= deg_x && q <= deg_y && r <= deg_z;
      var val := LegendrePolynomialExec(p, x[i]) * LegendrePolynomialExec(q, y[i]) * LegendrePolynomialExec(r, z[i]);
      row := row + [val];
      j := j + 1;
    }
    assert |row| == cols;
    result := result + [row];
    i := i + 1;
  }
}

// </vc-code>
