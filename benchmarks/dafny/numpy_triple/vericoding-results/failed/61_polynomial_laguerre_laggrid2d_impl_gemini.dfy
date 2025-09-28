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
/* helper modified by LLM (iteration 2): [implement laguerre polynomial evaluation] */
function lagval(n: nat, x: real): real 
  decreases n
{
    if n == 0 then 1.0
    else if n == 1 then 1.0 - x
    else 
        var n_real := n as real;
        ((2.0 * (n_real - 1.0) + 1.0 - x) * lagval(n - 1, x) - (n_real - 1.0) * lagval(n - 2, x)) / n_real
}

/* helper modified by LLM (iteration 2): [fix compilation error by using non-ghost evaluation] */
method ComputeSeriesValue(x_val: real, y_val: real, c: seq<seq<real>>) returns (res: real)
  requires |c| > 0
  requires forall i :: 0 <= i < |c| ==> |c[i]| > 0 && |c[i]| == |c[0]|
  ensures res == LaguerreSeriesValue(x_val, y_val, c)
{
  var rows := |c|;
  var cols := |c[0]|;
  var i := 0;
  res := 0.0;
  while i < rows
  {
    var j := 0;
    var row_sum: real := 0.0;
    while j < cols
    {
      var term_val := c[i][j] * lagval(i, x_val) * lagval(j, y_val);
      row_sum := row_sum + term_val;
      j := j + 1;
    }
    res := res + row_sum;
    i := i + 1;
  }
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
  /* code modified by LLM (iteration 2): [no changes from previous turn, structure is correct] */
  result := [];
  var i := 0;
  while i < |x|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> |result[k]| == |y|
    invariant forall k, l :: 0 <= k < i && 0 <= l < |y| ==> result[k][l] == LaguerreSeriesValue(x[k], y[l], c)
  {
    var row: seq<real> := [];
    var j := 0;
    while j < |y|
      invariant |row| == j
      invariant forall l :: 0 <= l < j ==> row[l] == LaguerreSeriesValue(x[i], y[l], c)
    {
      var val := ComputeSeriesValue(x[i], y[j], c);
      row := row + [val];
      j := j + 1;
    }
    result := result + [row];
    i := i + 1;
  }
}
// </vc-code>
