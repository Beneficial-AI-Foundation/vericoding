// <vc-preamble>
// Helper function to evaluate a Hermite polynomial at a point
// This is a mathematical specification of Hermite polynomial evaluation
ghost function HermitePolynomial(k: nat, x: real): real
  decreases k
{
  if k == 0 then 1.0
  else if k == 1 then 2.0 * x
  else 2.0 * x * HermitePolynomial(k-1, x) - 2.0 * (k-1) as real * HermitePolynomial(k-2, x)
}

// Evaluate a Hermite series with given coefficients at a point
ghost function EvaluateHermiteSeries(coeffs: seq<real>, x: real): real
  requires |coeffs| > 0
{
  EvaluateHermiteSeriesHelper(coeffs, x, 0)
}

ghost function EvaluateHermiteSeriesHelper(coeffs: seq<real>, x: real, i: nat): real
  requires |coeffs| > 0
  requires i <= |coeffs|
  decreases |coeffs| - i
{
  if i == |coeffs| then 0.0
  else coeffs[i] * HermitePolynomial(i, x) + EvaluateHermiteSeriesHelper(coeffs, x, i+1)
}

// Calculate sum of squared errors for given coefficients
ghost function SumSquaredError(x_vals: seq<real>, y_vals: seq<real>, coeffs: seq<real>): real
  requires |x_vals| == |y_vals|
  requires |x_vals| > 0
  requires |coeffs| > 0
{
  SumSquaredErrorHelper(x_vals, y_vals, coeffs, 0)
}

ghost function SumSquaredErrorHelper(x_vals: seq<real>, y_vals: seq<real>, coeffs: seq<real>, i: nat): real
  requires |x_vals| == |y_vals|
  requires |coeffs| > 0
  requires i <= |x_vals|
  decreases |x_vals| - i
{
  if i == |x_vals| then 0.0
  else
    var predicted := EvaluateHermiteSeries(coeffs, x_vals[i]);
    var error := y_vals[i] - predicted;
    error * error + SumSquaredErrorHelper(x_vals, y_vals, coeffs, i+1)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed ensures to use function calls with arguments */
function SwapRows(M: seq<seq<real>>, row1: int, row2: int): seq<seq<real>>
  requires 0 <= row1 < |M| && 0 <= row2 < |M|
  requires forall i :: 0 <= i < |M| ==> |M[i]| == |M[row1]|
  ensures |SwapRows(M, row1, row2)| == |M| && forall i :: 0 <= i < |M| ==> |SwapRows(M, row1, row2)[i]| == |M[i]|
  ensures SwapRows(M, row1, row2)[row1] == M[row2] && SwapRows(M, row1, row2)[row2] == M[row1]
  ensures forall i :: 0 <= i < |M| && i != row1 && i != row2 ==> SwapRows(M, row1, row2)[i] == M[i]
{
  M[row1 := M[row2]][row2 := M[row1]]
}

method ComputeVandermonde(x: seq<real>, cols: nat) returns (result: seq<seq<real>>)
  ensures |result| == |x| && forall i :: 0 <= i < |x| ==> |result[i]| == cols
{
/* helper modified by LLM (iteration 3): Changed from function to method to allow imperative implementation with for loops */
  var res : seq<seq<real>> := [];
  for i := 0 to |x|-1 {
    var row : seq<real> := [];
    for k := 0 to cols-1 {
      row := row + [HermitePolynomial(k, x[i])];
    }
    res := res + [row];
  }
  result := res;
}

method ComputeGram(x: seq<real>, deg: nat) returns (result: seq<seq<real>>)
  ensures |result| == deg+1 && forall i :: 0 <= i < |result| ==> |result[i]| == deg+1
{
/* helper modified by LLM (iteration 3): Changed from function to method to allow imperative implementation with for loops */
  var n := |x|;
  var len := deg + 1;
  var gram : seq<seq<real>> := [];
  for i := 0 to len-1 {
    var row : seq<real> := [];
    for j := 0 to len-1 {
      row := row + [0.0];
    }
    gram := gram + [row];
  }
  for k := 0 to n-1 {
    for p := 0 to deg {
      for q := 0 to deg {
        var coef := HermitePolynomial(p, x[k]) * HermitePolynomial(q, x[k]);
        gram := gram[p := gram[p][q := gram[p][q] + coef]];
      }
    }
  }
  result := gram;
}

method ComputeBVector(x: seq<real>, y: seq<real>, deg: nat) returns (result: seq<real>)
  requires |x| == |y|
  ensures |result| == deg+1
{
/* helper modified by LLM (iteration 3): Changed from function to method to allow imperative implementation with for loops */
  var n := |x|;
  var b : seq<real> := [];
  for k := 0 to deg {
    b := b + [0.0];
  }
  for i := 0 to n-1 {
    for k := 0 to deg {
      b := b[k := b[k] + y[i] * HermitePolynomial(k, x[i])];
    }
  }
  result := b;
}

method SolveLinear(A: seq<seq<real>>, b: seq<real>) returns (x: seq<real>)
  requires |A| > 0 && (forall i :: 0 <= i < |A| ==> |A[i]| == |A|) && |b| == |A|
  ensures |x| == |A|
{
  /* code modified by LLM (iteration 3): Implemented matrix operations using immutable seq updates */
  var n := |A|;
  var M : seq<seq<real>> := [];
  for i := 0 to n-1 {
    M := M + [A[i] + [b[i]]];
  }
  // Forward elimination with pivoting
  for p := 0 to n-1 {
    var max_row := p;
    for i := p+1 to n-1 {
      if M[i][p] * M[i][p] > M[max_row][p] * M[max_row][p] {
        max_row := i;
      }
    }
    // Swap rows
    if max_row != p {
      M := SwapRows(M, p, max_row);
    }
    // Eliminate
    for i := p+1 to n-1 {
      var factor := M[i][p] / M[p][p];
      var new_row : seq<real> := [];
      for j := 0 to n {
        new_row := new_row + [M[i][j] - factor * M[p][j]];
      }
      M := M[i := new_row];
    }
  }
  // Back substitution
  var x0 : seq<real> := [];
  for i := 0 to n-1 {
    x0 := x0 + [0.0];
  }
  for i := n downto 1 {
    var sum := 0.0;
    for j := i+1 to n {
      var j_idx := j as nat;
      sum := sum + M[i][j] * x0[j_idx];
    }
    var i_idx := i as nat;
    x0 := x0[i_idx := (M[i][n] - sum) / M[i][i]];
  }
  x := x0;
}
// </vc-helpers>

// <vc-spec>
method hermfit(x: seq<real>, y: seq<real>, deg: nat) returns (coeff: seq<real>)
  requires |x| == |y|
  requires |x| > 0
  requires deg >= 0
  
  ensures |coeff| == deg + 1
  ensures deg + 1 > 0
  
  // Least squares optimality property: the returned coefficients minimize
  // the sum of squared errors compared to any other coefficient vector
  ensures forall other_coeffs: seq<real> :: 
    |other_coeffs| == deg + 1 ==>
    SumSquaredError(x, y, coeff) <= SumSquaredError(x, y, other_coeffs)
  
  // For interpolation case: when number of points equals degree + 1,
  // and points are distinct, the polynomial passes through all points exactly
  ensures |x| == deg + 1 && (forall i, j :: 0 <= i < j < |x| ==> x[i] != x[j]) ==>
    forall i :: 0 <= i < |x| ==> EvaluateHermiteSeries(coeff, x[i]) == y[i]
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 4): Removed shadow local variable coeff to avoid duplicate name error, assigning directly to out parameter */
  var deg_plus := deg + 1;
  coeff := [];
  if deg_plus == 1 {
    var sum_y := 0.0;
    for i := 0 to |x|-1 {
      sum_y := sum_y + y[i];
    }
    coeff := [sum_y / (|x| as real)];
  } else {
    var V := ComputeVandermonde(x, deg_plus);
    if |x| == deg_plus {
      coeff := SolveLinear(V, y);
    } else {
      var gram := ComputeGram(x, deg);
      var bvec := ComputeBVector(x, y, deg);
      coeff := SolveLinear(gram, bvec);
    }
  }
}
// </vc-code>
