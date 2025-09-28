// <vc-preamble>
// Ghost function to represent the n-th Laguerre polynomial L_n(x)
ghost function LaguerrePolynomial(n: nat, x: real): real

// Ghost function to compute the sum of a 2D Laguerre series at a specific point
ghost function LaguerreSeriesValue(x: real, y: real, c: seq<seq<real>>): real
  requires |c| > 0
  requires forall i :: 0 <= i < |c| ==> |c[i]| > 0
  requires forall i :: 0 <= i < |c| ==> |c[i]| == |c[0]|
{
  var rows := |c|;
  var cols := |c[0]|;
  
  // Sum over all coefficient terms: ∑_{i,j} c[i][j] * L_i(x) * L_j(y)
  SumOverCoefficients(x, y, c, 0, 0, rows, cols)
}

// Helper ghost function for double summation
ghost function SumOverCoefficients(x: real, y: real, c: seq<seq<real>>, i: nat, j: nat, rows: nat, cols: nat): real
  requires |c| == rows > 0
  requires forall k :: 0 <= k < |c| ==> |c[k]| == cols > 0
  requires 0 <= i <= rows
  requires 0 <= j <= cols
  decreases rows - i, cols - j
{
  if i >= rows then 0.0
  else if j >= cols then SumOverCoefficients(x, y, c, i + 1, 0, rows, cols)
  else c[i][j] * LaguerrePolynomial(i, x) * LaguerrePolynomial(j, y) + 
       SumOverCoefficients(x, y, c, i, j + 1, rows, cols)
}
// </vc-preamble>

// <vc-helpers>
function LaguerrePolynomial(n: nat, x: real): real
  ensures n == 0 ==> LaguerrePolynomial(n, x) == 1.0
  ensures n == 1 ==> LaguerrePolynomial(n, x) == 1.0 - x
  decreases n
{
  if n == 0 then 1.0
  else if n == 1 then 1.0 - x
  else ((2.0 * real(n) - 1.0 - x) * LaguerrePolynomial(n - 1, x) - real(n - 1) * LaguerrePolynomial(n - 2, x)) / real(n)
}

lemma LaguerreSeriesDefinition(x: real, y: real, c: seq<seq<real>>)
  requires |c| > 0
  requires forall i :: 0 <= i < |c| ==> |c[i]| > 0
  requires forall i :: 0 <= i < |c| ==> |c[i]| == |c[0]|
{
}
// </vc-helpers>

// <vc-spec>
method laggrid2d(x: seq<real>, y: seq<real>, c: seq<seq<real>>) returns (result: seq<seq<real>>)
  // Preconditions
  requires |x| > 0                                    // x sequence must be non-empty
  requires |y| > 0                                    // y sequence must be non-empty
  requires |c| > 0                                    // coefficient matrix has rows
  requires forall i :: 0 <= i < |c| ==> |c[i]| > 0   // coefficient matrix has columns
  requires forall i :: 0 <= i < |c| ==> |c[i]| == |c[0]|  // all rows have same length
  
  // Postconditions
  ensures |result| == |x|                             // result has same number of rows as x elements
  ensures forall i :: 0 <= i < |result| ==> |result[i]| == |y|  // each row has same length as y
  ensures forall i, j :: 0 <= i < |x| && 0 <= j < |y| ==>      // each element is the Laguerre series evaluation
    result[i][j] == LaguerreSeriesValue(x[i], y[j], c)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Fixed compilation error in LaguerrePolynomial expression */
  result := new real[|x|];
  var i := 0;
  while i < |x|
    invariant i <= |x|
    invariant |result| == |x|
    invariant forall k :: 0 <= k < i ==> |result[k]| == |y|
    invariant forall k, l :: 0 <= k < i && 0 <= l < |y| ==> result[k][l] == LaguerreSeriesValue(x[k], y[l], c)
  {
    result[i] := new real[|y|];
    var j := 0;
    while j < |y|
      invariant j <= |y|
      invariant |result[i]| == |y|
      invariant forall l :: 0 <= l < j ==> result[i][l] == LaguerreSeriesValue(x[i], y[l], c)
    {
      result[i][j] := LaguerreSeriesValue(x[i], y[j], c);
      j := j + 1;
    }
    i := i + 1;
  }
}
// </vc-code>
