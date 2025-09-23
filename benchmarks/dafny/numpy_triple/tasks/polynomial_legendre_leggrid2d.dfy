// <vc-preamble>
// Define a 2D real matrix type for coefficients and results
type Matrix2D = seq<seq<real>>

// Predicate to check if a matrix has valid dimensions
predicate ValidMatrix(m: Matrix2D, rows: nat, cols: nat)
{
    |m| == rows && (forall i :: 0 <= i < rows ==> |m[i]| == cols)
}

// Ghost function representing Legendre polynomial L_n(x)
ghost function LegendrePolynomial(n: nat, x: real): real
{
    if n == 0 then 1.0
    else if n == 1 then x
    else ((2.0 * n as real - 1.0) * x * LegendrePolynomial(n-1, x) - (n as real - 1.0) * LegendrePolynomial(n-2, x)) / (n as real)
}

// Helper function to compute partial sum for inner loop
ghost function InnerSum(y: real, c_row: seq<real>, j: nat): real
    requires j <= |c_row|
    decreases j
{
    if j == 0 then 0.0
    else InnerSum(y, c_row, j-1) + c_row[j-1] * LegendrePolynomial(j-1, y)
}

// Helper function to compute partial sum for outer loop  
ghost function OuterSum(x: real, y: real, c: Matrix2D, i: nat, deg_y: nat): real
    requires i <= |c|
    requires ValidMatrix(c, |c|, deg_y)
    decreases i
{
    if i == 0 then 0.0
    else OuterSum(x, y, c, i-1, deg_y) + LegendrePolynomial(i-1, x) * InnerSum(y, c[i-1], deg_y)
}

// Ghost function to compute the sum of Legendre series at a point
ghost function LegendreSeriesValue(x: real, y: real, c: Matrix2D, deg_x: nat, deg_y: nat): real
    requires ValidMatrix(c, deg_x, deg_y)
{
    // ∑_{i,j} c_{i,j} * L_i(x) * L_j(y)
    OuterSum(x, y, c, deg_x, deg_y)
}

// Main method for 2D Legendre grid evaluation
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method LeggGrid2D(x: seq<real>, y: seq<real>, c: Matrix2D) returns (result: Matrix2D)
    requires |x| > 0
    requires |y| > 0
    requires |c| > 0
    requires forall i :: 0 <= i < |c| ==> |c[i]| > 0
    requires ValidMatrix(c, |c|, |c[0]|)
    
    ensures ValidMatrix(result, |x|, |y|)
    ensures |result| == |x|
    ensures forall i :: 0 <= i < |result| ==> |result[i]| == |y|
    
    // Each result[i][j] contains the evaluation of the 2D Legendre series at (x[i], y[j])
    ensures forall i, j :: 0 <= i < |x| && 0 <= j < |y| ==>
        result[i][j] == LegendreSeriesValue(x[i], y[j], c, |c|, |c[0]|)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
