// <vc-preamble>
// Ghost function to represent the value of the i-th Laguerre polynomial at point x
ghost function LaguerrePolynomial(i: nat, x: real): real

// Ghost function to compute the 2D Laguerre series evaluation at a single point
ghost function Lagval2DSinglePoint(x: real, y: real, c: seq<seq<real>>): real
  requires |c| > 0
  requires forall i :: 0 <= i < |c| ==> |c[i]| > 0
{
  var nx := |c| - 1;
  var ny := |c[0]| - 1;
  SumOverIndices(0, nx, 0, ny, x, y, c)
}

// Ghost function to compute the double sum over all coefficient indices
ghost function SumOverIndices(i_start: nat, i_end: nat, j_start: nat, j_end: nat, 
                             x: real, y: real, c: seq<seq<real>>): real
  requires i_start <= i_end + 1
  requires j_start <= j_end + 1
  requires |c| > i_end
  requires forall k :: 0 <= k < |c| ==> |c[k]| > j_end
{
  if i_start > i_end then 0.0
  else SumOverJ(i_start, j_start, j_end, x, y, c) + 
       SumOverIndices(i_start + 1, i_end, j_start, j_end, x, y, c)
}

// Ghost function to compute the sum over j indices for a fixed i
ghost function SumOverJ(i: nat, j_start: nat, j_end: nat, 
                       x: real, y: real, c: seq<seq<real>>): real
  requires j_start <= j_end + 1
  requires i < |c|
  requires forall k :: 0 <= k < |c| ==> |c[k]| > j_end
{
  if j_start > j_end then 0.0
  else c[i][j_start] * LaguerrePolynomial(i, x) * LaguerrePolynomial(j_start, y) +
       SumOverJ(i, j_start + 1, j_end, x, y, c)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method lagval2d(x: seq<real>, y: seq<real>, c: seq<seq<real>>) returns (result: seq<real>)
  // Input validation requirements
  requires |x| == |y|  // x and y must have the same length
  requires |c| > 0     // coefficient matrix must be non-empty
  requires forall i :: 0 <= i < |c| ==> |c[i]| > 0  // all rows must be non-empty
  requires forall i :: 0 <= i < |c| ==> |c[i]| == |c[0]|  // all rows must have same length
  
  // Output guarantees
  ensures |result| == |x|  // result has same length as input vectors
  ensures |result| == |y|  // result has same length as input vectors
  
  // Functional correctness: each result element is the 2D Laguerre evaluation
  ensures forall i :: 0 <= i < |result| ==> 
    result[i] == Lagval2DSinglePoint(x[i], y[i], c)
  
  // Base case: when coefficient matrix is 1x1, result is constant
  ensures |c| == 1 && |c[0]| == 1 ==> 
    forall i :: 0 <= i < |result| ==> result[i] == c[0][0]
  
  // Mathematical relationship: result represents bivariate polynomial evaluation
  ensures forall i :: 0 <= i < |result| ==> 
    result[i] == SumOverIndices(0, |c| - 1, 0, |c[0]| - 1, x[i], y[i], c)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
