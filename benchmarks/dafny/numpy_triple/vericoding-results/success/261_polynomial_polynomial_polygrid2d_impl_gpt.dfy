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
/* helper modified by LLM (iteration 4): build a row sequence recursively with length and element-wise guarantees */
function EvaluateRowBuild(xi: real, y: seq<real>, c: seq<seq<real>>, idx: nat): seq<real>
    requires |c| > 0
    requires forall i :: 0 <= i < |c| ==> |c[i]| > 0
    requires forall i :: 0 <= i < |c| ==> |c[i]| == |c[0]|
    requires idx <= |y|
    ensures |EvaluateRowBuild(xi, y, c, idx)| == idx
    ensures forall j :: 0 <= j < idx ==> EvaluateRowBuild(xi, y, c, idx)[j] == EvaluatePolynomial2D(xi, y[j], c)
    decreases idx
{
    if idx == 0 then []
    else EvaluateRowBuild(xi, y, c, idx - 1) + [EvaluatePolynomial2D(xi, y[idx - 1], c)]
}

/* helper modified by LLM (iteration 4): wrapper that builds a full row for a given xi */
function EvaluateRow(xi: real, y: seq<real>, c: seq<seq<real>>): seq<real>
    requires |c| > 0
    requires forall i :: 0 <= i < |c| ==> |c[i]| > 0
    requires forall i :: 0 <= i < |c| ==> |c[i]| == |c[0]|
    ensures |EvaluateRow(xi, y, c)| == |y|
    ensures forall j :: 0 <= j < |y| ==> EvaluateRow(xi, y, c)[j] == EvaluatePolynomial2D(xi, y[j], c)
{
    EvaluateRowBuild(xi, y, c, |y|)
}
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
  /* code modified by LLM (iteration 4): build grid iteratively using EvaluateRow helper and invariants */
  var res: seq<seq<real>> := [];
  var i: nat := 0;
  while i < |x|
    invariant 0 <= i <= |x|
    invariant |res| == i
    invariant forall k :: 0 <= k < |res| ==> |res[k]| == |y|
    invariant forall k, j :: 0 <= k < |res| && 0 <= j < |y| ==> res[k][j] == EvaluatePolynomial2D(x[k], y[j], c)
  {
    res := res + [EvaluateRow(x[i], y, c)];
    i := i + 1;
  }
  result := res;
}
// </vc-code>
