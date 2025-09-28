// <vc-preamble>
/*
 * 2D Polynomial Grid Evaluation
 * 
 * This file provides a specification for evaluating a 2-D polynomial on the Cartesian 
 * product of x and y coordinates, producing a grid of results where each point 
 * represents the polynomial evaluation at the corresponding (x[i], y[j]) coordinate pair.
 */

// Helper function to compute real number powers
function Power(base: real, exp: nat): real
    decreases exp
{
    if exp == 0 then 1.0
    else base * Power(base, exp - 1)
}

// Helper function to evaluate a 2D polynomial at a single point (a, b)
// Formula: p(a,b) = sum_{i,j} c[i][j] * a^i * b^j
function EvaluatePolynomial2D(a: real, b: real, c: seq<seq<real>>): real
    requires |c| > 0
    requires forall i :: 0 <= i < |c| ==> |c[i]| > 0
    requires forall i :: 0 <= i < |c| ==> |c[i]| == |c[0]|  // All rows have same length
{
    EvaluatePolynomial2DHelper(a, b, c, 0, 0, 0.0)
}

// Helper function for polynomial evaluation with accumulator
function EvaluatePolynomial2DHelper(a: real, b: real, c: seq<seq<real>>, 
                                  row: nat, col: nat, acc: real): real
    requires |c| > 0
    requires forall i :: 0 <= i < |c| ==> |c[i]| > 0
    requires forall i :: 0 <= i < |c| ==> |c[i]| == |c[0]|
    decreases |c| - row, |c[0]| - col
{
    if row >= |c| then acc
    else if col >= |c[0]| then 
        EvaluatePolynomial2DHelper(a, b, c, row + 1, 0, acc)
    else
        var term := c[row][col] * Power(a, row) * Power(b, col);
        EvaluatePolynomial2DHelper(a, b, c, row, col + 1, acc + term)
}

// Main method for 2D polynomial grid evaluation
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method PolyGrid2D(x: seq<real>, y: seq<real>, c: seq<seq<real>>) 
    returns (result: seq<seq<real>>)
    requires |c| > 0                                           // At least one row of coefficients
    requires forall i :: 0 <= i < |c| ==> |c[i]| > 0          // Each row has at least one coefficient
    requires forall i :: 0 <= i < |c| ==> |c[i]| == |c[0]|    // All coefficient rows have same length
    ensures |result| == |x|                                    // Result has same number of rows as x values
    ensures forall i :: 0 <= i < |result| ==> |result[i]| == |y|  // Each result row has same length as y
    ensures forall i, j :: 0 <= i < |x| && 0 <= j < |y| ==>   // Each result value is the polynomial evaluation
        result[i][j] == EvaluatePolynomial2D(x[i], y[j], c)
// </vc-spec>
// <vc-code>
{
  result := [];
  var i := 0;
  while i < |x|
    invariant 0 <= i <= |x|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> |result[k]| == |y|
    invariant forall k, j :: 0 <= k < i && 0 <= j < |y| ==> result[k][j] == EvaluatePolynomial2D(x[k], y[j], c)
  {
    var row := [];
    var j := 0;
    while j < |y|
      invariant 0 <= j <= |y|
      invariant |row| == j
      invariant forall m :: 0 <= m < j ==> row[m] == EvaluatePolynomial2D(x[i], y[m], c)
    {
      var val := EvaluatePolynomial2D(x[i], y[j], c);
      row := row + [val];
      j := j + 1;
    }
    result := result + [row];
    i := i + 1;
  }
}
// </vc-code>
