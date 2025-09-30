// <vc-preamble>
/*
 * Pseudo-Vandermonde matrix construction for 2D Legendre polynomials.
 * This module defines functionality to construct a 2D pseudo-Vandermonde matrix
 * where each entry is the product of Legendre polynomial evaluations at given sample points.
 */

// Function to evaluate the k-th Legendre polynomial at point x
// L_0(x) = 1, L_1(x) = x, etc.
function LegendrePolynomial(k: nat, x: real): real
{
  if k == 0 then 1.0 else 0.0  // placeholder implementation
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Provide division/modulo nonnegativity and bounds facts. */
lemma DivModFacts(b: int, j: int)
  requires 0 < b
  requires 0 <= j
  ensures 0 <= j / b
  ensures 0 <= j % b < b
{
}

/* helper modified by LLM (iteration 4): Linear index bound: b*p+q < (deg_x+1)*b when 0<=p<=deg_x and 0<=q<b. */
lemma IndexUpperBound(b: int, deg_x: int, p: int, q: int)
  requires 0 < b
  requires 0 <= p <= deg_x
  requires 0 <= q < b
  ensures b * p + q < (deg_x + 1) * b
{
}

// </vc-helpers>

// <vc-spec>
method legvander2d(x: seq<real>, y: seq<real>, deg_x: nat, deg_y: nat) 
  returns (result: seq<seq<real>>)
  requires |x| == |y|
  requires |x| > 0
  ensures |result| == |x|
  ensures forall i :: 0 <= i < |result| ==> |result[i]| == (deg_x + 1) * (deg_y + 1)
  // First column corresponds to L_0(x) * L_0(y) = 1 * 1 = 1
  ensures forall i :: 0 <= i < |result| ==> result[i][0] == 1.0
  // Each entry at position [i][col] where col = (deg_y + 1)*p + q 
  // equals L_p(x[i]) * L_q(y[i]) for valid p, q
  ensures forall i, p, q :: 
    0 <= i < |result| && 
    0 <= p <= deg_x && 
    0 <= q <= deg_y ==>
    (deg_y + 1) * p + q < |result[i]| && 
    result[i][(deg_y + 1) * p + q] == LegendrePolynomial(p, x[i]) * LegendrePolynomial(q, y[i])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): Construct the 2D pseudo-Vandermonde matrix row by row using column-wise mapping via div/mod. */
  var n := |x|;
  var b: int := deg_y + 1;
  var m: int := (deg_x + 1) * b;
  assert 0 < b;

  result := [];
  var i := 0;
  while i < n
    invariant 0 < b
    invariant 0 <= i <= n
    invariant |result| == i
    invariant forall k :: 0 <= k < |result| ==> |result[k]| == m
    invariant forall k :: 0 <= k < |result| ==>
               forall col :: 0 <= col < |result[k]| ==>
                 result[k][col] ==
                   LegendrePolynomial((col / b) as nat, x[k]) *
                   LegendrePolynomial((col % b) as nat, y[k])
    decreases n - i
  {
    var row: seq<real> := [];
    var j := 0;
    while j < m
      invariant 0 < b
      invariant 0 <= j <= m
      invariant |row| == j
      invariant forall col :: 0 <= col < |row| ==>
                 row[col] ==
                   LegendrePolynomial((col / b) as nat, x[i]) *
                   LegendrePolynomial((col % b) as nat, y[i])
      decreases m - j
    {
      assert 0 <= j / b;
      assert 0 <= j % b;
      assert j % b < b;
      var value := LegendrePolynomial((j / b) as nat, x[i]) *
                   LegendrePolynomial((j % b) as nat, y[i]);
      row := row + [value];
      j := j + 1;
    }
    assert |row| == m;
    result := result + [row];
    i := i + 1;
  }
}
// </vc-code>
