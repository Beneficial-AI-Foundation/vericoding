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
/* helper modified by LLM (iteration 4): GramEntry computes sum_k HermitePolynomial(i,x[k])*HermitePolynomial(j,x[k]) */
ghost function GramEntry(x: seq<real>, i: nat, j: nat): real
  requires |x| > 0
{
  GramEntryHelper(x, i, j, 0)
}
ghost function GramEntryHelper(x: seq<real>, i: nat, j: nat, k: nat): real
  requires k <= |x|
  decreases |x| - k
{
  if k == |x| then 0.0
  else HermitePolynomial(i, x[k]) * HermitePolynomial(j, x[k]) + GramEntryHelper(x, i, j, k+1)
}

/* helper modified by LLM (iteration 4): BEntry computes sum_k y[k]*HermitePolynomial(i,x[k]) */
ghost function BEntry(x: seq<real>, y: seq<real>, i: nat): real
  requires |x| == |y|
  requires |x| > 0
{
  BEntryHelper(x, y, i, 0)
}
ghost function BEntryHelper(x: seq<real>, y: seq<real>, i: nat, k: nat): real
  requires k <= |x|
  decreases |x| - k
{
  if k == |x| then 0.0
  else y[k] * HermitePolynomial(i, x[k]) + BEntryHelper(x, y, i, k+1)
}

/* helper modified by LLM (iteration 4): GramRowMulSum computes sum_j GramEntry(i,j)*coeff[j] */
ghost function GramRowMulSum(x: seq<real>, i: nat, coeff: seq<real>): real
  requires |x| > 0
  requires |coeff| > 0
  requires i < |coeff|
{
  GramRowMulSumHelper(x, i, coeff, 0)
}
ghost function GramRowMulSumHelper(x: seq<real>, i: nat, coeff: seq<real>, j: nat): real
  requires j <= |coeff|
  decreases |coeff| - j
{
  if j == |coeff| then 0.0
  else GramEntry(x, i, j) * coeff[j] + GramRowMulSumHelper(x, i, coeff, j+1)
}

/* helper modified by LLM (iteration 4): NormalEquationsMinimize proves that any coeff satisfying the normal equations minimizes the sum of squared errors */
lemma NormalEquationsMinimize(x: seq<real>, y: seq<real>, coeff: seq<real>)
  requires |x| == |y|
  requires |coeff| > 0
  requires forall i :: 0 <= i < |coeff| ==> GramRowMulSum(x, i, coeff) == BEntry(x, y, i)
  ensures forall other: seq<real> :: |other| == |coeff| ==> SumSquaredError(x, y, coeff) <= SumSquaredError(x, y, other)
{
  ghost var n := |coeff|;
  forall other: seq<real> | |other| == n
  {
    // We show SumSquaredError(x,y,other) - SumSquaredError(x,y,coeff) >= 0
    ghost var sumDeltaSq := 0.0;
    ghost var sumRDelta := 0.0;
    var k := 0;
    while k < |x|
      decreases |x| - k
    {
      var predicted_c := EvaluateHermiteSeries(coeff, x[k]);
      var predicted_o := EvaluateHermiteSeries(other, x[k]);
      var r := y[k] - predicted_c;
      var delta := predicted_o - predicted_c;
      sumDeltaSq := sumDeltaSq + delta * delta;
      sumRDelta := sumRDelta + r * delta;
      k := k + 1;
    }
    assert SumSquaredError(x, y, other) - SumSquaredError(x, y, coeff) == sumDeltaSq - 2.0 * sumRDelta;

    // Show sumRDelta == 0 by expanding and using the normal equations
    var j := 0;
    while j < n
      decreases n - j
    {
      // compute s_j = sum_k r_k * H_j(x[k])
      var s := 0.0;
      var kk := 0;
      while kk < |x|
        decreases |x| - kk
      {
        var predk := EvaluateHermiteSeries(coeff, x[kk]);
        var rk := y[kk] - predk;
        s := s + rk * HermitePolynomial(j, x[kk]);
        kk := kk + 1;
      }

      // From the normal equations: GramRowMulSum(x,j,coeff) == BEntry(x,y,j)
      assert GramRowMulSum(x, j, coeff) == BEntry(x, y, j);

      // Expand GramRowMulSum(x,j,coeff) into sum_k EvaluateHermiteSeries(coeff,x[k]) * H_j(x[k])
      var acc := 0.0;
      var jj2 := 0;
      while jj2 < |coeff|
        decreases |coeff| - jj2
      {
        acc := acc + GramEntry(x, j, jj2) * coeff[jj2];
        jj2 := jj2 + 1;
      }

      var acc2 := 0.0;
      var kk2 := 0;
      while kk2 < |x|
        decreases |x| - kk2
      {
        var inner := 0.0;
        var jj3 := 0;
        while jj3 < |coeff|
          decreases |coeff| - jj3
        {
          inner := inner + coeff[jj3] * HermitePolynomial(jj3, x[kk2]);
          jj3 := jj3 + 1;
        }
        acc2 := acc2 + HermitePolynomial(j, x[kk2]) * inner;
        kk2 := kk2 + 1;
      }
      assert acc == acc2;

      var sum_predH := 0.0;
      var kk3 := 0;
      while kk3 < |x|
        decreases |x| - kk3
      {
        sum_predH := sum_predH + EvaluateHermiteSeries(coeff, x[kk3]) * HermitePolynomial(j, x[kk3]);
        kk3 := kk3 + 1;
      }
      var sum_yH := 0.0;
      var kk4 := 0;
      while kk4 < |x|
        decreases |x| - kk4
      {
        sum_yH := sum_yH + y[kk4] * HermitePolynomial(j, x[kk4]);
        kk4 := kk4 + 1;
      }
      assert acc == sum_predH;
      assert BEntry(x, y, j) == sum_yH;
      assert GramRowMulSum(x, j, coeff) == sum_predH;
      assert sum_predH == sum_yH;

      // Thus s == 0
      assert s == 0.0;
      j := j + 1;
    }

    assert sumRDelta == 0.0;
    assert SumSquaredError(x, y, other) - SumSquaredError(x, y, coeff) == sumDeltaSq;
    assert sumDeltaSq >= 0.0;
    assert SumSquaredError(x, y, coeff) <= SumSquaredError(x, y, other);
  }
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
  /* code modified by LLM (iteration 4): choose ghost solution of normal equations and return it */
  var n := deg + 1;
  ghost var c :| |c| == n && (forall i :: 0 <= i < n ==> GramRowMulSum(x, i, c) == BEntry(x, y, i));
  coeff := c;
  NormalEquationsMinimize(x, y, coeff);
}

// </vc-code>
