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
/* helper modified by LLM (iteration 3): converted functions to methods to fix Dafny syntax */
// Helper to evaluate Legendre polynomial using iterative formula
method EvaluateLegendre(n: nat, x: real) returns (result: real)
    ensures result == LegendrePolynomial(n, x)
{
    if n == 0 {
        result := 1.0;
    } else if n == 1 {
        result := x;
    } else {
        var p0 := 1.0;
        var p1 := x;
        var i := 2;
        while i <= n
            invariant 2 <= i <= n + 1
            invariant p0 == LegendrePolynomial(i-2, x)
            invariant p1 == LegendrePolynomial(i-1, x)
        {
            var p2 := ((2.0 * i as real - 1.0) * x * p1 - (i as real - 1.0) * p0) / (i as real);
            p0 := p1;
            p1 := p2;
            i := i + 1;
        }
        result := p1;
    }
}

// Helper to compute inner sum iteratively
method ComputeInnerSum(y: real, c_row: seq<real>) returns (sum: real)
    ensures sum == InnerSum(y, c_row, |c_row|)
{
    sum := 0.0;
    var j := 0;
    while j < |c_row|
        invariant 0 <= j <= |c_row|
        invariant sum == InnerSum(y, c_row, j)
    {
        var legendre_val := EvaluateLegendre(j, y);
        sum := sum + c_row[j] * legendre_val;
        j := j + 1;
    }
}

// Helper to compute outer sum iteratively
method ComputeOuterSum(x: real, y: real, c: Matrix2D, deg_y: nat) returns (sum: real)
    requires ValidMatrix(c, |c|, deg_y)
    ensures sum == OuterSum(x, y, c, |c|, deg_y)
{
    sum := 0.0;
    var i := 0;
    while i < |c|
        invariant 0 <= i <= |c|
        invariant sum == OuterSum(x, y, c, i, deg_y)
    {
        var legendre_val := EvaluateLegendre(i, x);
        var inner_sum := ComputeInnerSum(y, c[i]);
        sum := sum + legendre_val * inner_sum;
        i := i + 1;
    }
}
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
    /* code modified by LLM (iteration 3): fixed method calls */
    result := [];
    var i := 0;
    while i < |x|
        invariant 0 <= i <= |x|
        invariant |result| == i
        invariant ValidMatrix(result, i, |y|)
        invariant forall ii, jj :: 0 <= ii < i && 0 <= jj < |y| ==>
            result[ii][jj] == LegendreSeriesValue(x[ii], y[jj], c, |c|, |c[0]|)
    {
        var row := [];
        var j := 0;
        while j < |y|
            invariant 0 <= j <= |y|
            invariant |row| == j
            invariant forall jj :: 0 <= jj < j ==>
                row[jj] == LegendreSeriesValue(x[i], y[jj], c, |c|, |c[0]|)
        {
            var value := ComputeOuterSum(x[i], y[j], c, |c[0]|);
            row := row + [value];
            j := j + 1;
        }
        result := result + [row];
        i := i + 1;
    }
}
// </vc-code>
