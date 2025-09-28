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
method ComputeLegendrePolynomial(n: nat, x: real) returns (res: real)
    ensures res == LegendrePolynomial(n, x)
{
    if n == 0 {
        return 1.0;
    } else if n == 1 {
        return x;
    } else {
        var l_prev := 1.0;
        var l_curr := x;
        var i := 2;
        while i <= n
            decreases n - i
            invariant 2 <= i <= n + 1
            invariant l_prev == LegendrePolynomial(i - 2, x)
            invariant l_curr == LegendrePolynomial(i - 1, x)
        {
            var l_next := ((2.0 * (i as real) - 1.0) * x * l_curr - ((i as real) - 1.0) * l_prev) / (i as real);
            l_prev := l_curr;
            l_curr := l_next;
            i := i + 1;
        }
        return l_curr;
    }
}

method ComputeLegendreSeries1D(y: real, c_row: seq<real>) returns (res: real)
    ensures res == InnerSum(y, c_row, |c_row|)
{
    var sum: real := 0.0;
    var j := 0;
    while j < |c_row|
        decreases |c_row| - j
        invariant 0 <= j <= |c_row|
        invariant sum == InnerSum(y, c_row, j)
    {
        var lj := ComputeLegendrePolynomial(j, y);
        sum := sum + c_row[j] * lj;
        j := j + 1;
    }
    return sum;
}

method ComputeLegendreSeries2D(x_val: real, y_val: real, c: Matrix2D) returns (res: real)
    requires |c| > 0
    requires ValidMatrix(c, |c|, |c[0]|)
    ensures res == LegendreSeriesValue(x_val, y_val, c, |c|, |c[0]|)
{
    var sum: real := 0.0;
    var i := 0;
    var deg_x := |c|;
    var deg_y := |c[0]|;
    while i < deg_x
        decreases deg_x - i
        invariant 0 <= i <= deg_x
        invariant ValidMatrix(c, deg_x, deg_y)
        invariant sum == OuterSum(x_val, y_val, c, i, deg_y)
    {
        var li := ComputeLegendrePolynomial(i, x_val);
        var inner_sum_val := ComputeLegendreSeries1D(y_val, c[i]);
        sum := sum + li * inner_sum_val;
        i := i + 1;
    }
    return sum;
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
  var nx := |x|;
  var ny := |y|;
  var deg_x := |c|;
  var deg_y := |c[0]|;

  var temp_result: Matrix2D := [];
  var i := 0;
  while i < nx
    decreases nx - i
    invariant 0 <= i <= nx
    invariant |temp_result| == i
    invariant forall k :: 0 <= k < i ==> |temp_result[k]| == ny
    invariant forall i_loop, j_loop :: 0 <= i_loop < i && 0 <= j_loop < ny ==>
      temp_result[i_loop][j_loop] == LegendreSeriesValue(x[i_loop], y[j_loop], c, deg_x, deg_y)
  {
    var row: seq<real> := [];
    var j := 0;
    while j < ny
      decreases ny - j
      invariant 0 <= j <= ny
      invariant |row| == j
      invariant forall j_loop :: 0 <= j_loop < j ==> 
        row[j_loop] == LegendreSeriesValue(x[i], y[j_loop], c, deg_x, deg_y)
    {
      var val := ComputeLegendreSeries2D(x[i], y[j], c);
      row := row + [val];
      j := j + 1;
    }
    temp_result := temp_result + [row];
    i := i + 1;
  }
  result := temp_result;
}
// </vc-code>
