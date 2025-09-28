// <vc-preamble>
/*
 * Dafny specification for numpy.corrcoef: Pearson product-moment correlation coefficients.
 * 
 * This module defines the computation of correlation coefficients between two vectors,
 * measuring the linear relationship between variables. The correlation coefficient
 * normalizes covariance by the product of standard deviations, yielding a value
 * bounded between -1 and 1.
 */

// Helper function to compute the mean of a sequence
function mean(values: seq<real>): real
  requires |values| > 0
{
  sum(values) / |values| as real
}

// Helper function to compute the sum of a sequence
function sum(values: seq<real>): real
{
  if |values| == 0 then 0.0
  else values[0] + sum(values[1..])
}

// Helper function to compute covariance between two sequences
function covariance(x: seq<real>, y: seq<real>): real
  requires |x| > 0
  requires |y| > 0
  requires |x| == |y|
{
  var mean_x := mean(x);
  var mean_y := mean(y);
  var deviations := seq(|x|, i requires 0 <= i < |x| => (x[i] - mean_x) * (y[i] - mean_y));
  sum(deviations) / |x| as real
}

// Helper function to compute variance of a sequence
function variance(values: seq<real>): real
  requires |values| > 0
{
  var mean_val := mean(values);
  var squared_deviations := seq(|values|, i requires 0 <= i < |values| => (values[i] - mean_val) * (values[i] - mean_val));
  sum(squared_deviations) / |values| as real
}

// Helper function to compute standard deviation
function standardDeviation(values: seq<real>): real
  requires |values| > 0
  requires variance(values) > 0.0
{
  // In specification, we assume sqrt function exists
  sqrt(variance(values))
}

// Predicate to check if a sequence has non-zero variance
predicate hasNonZeroVariance(values: seq<real>)
  requires |values| > 0
{
  exists i, j :: 0 <= i < |values| && 0 <= j < |values| && values[i] != values[j]
}

// Specification-only sqrt function for standard deviation computation
function {:axiom} sqrt(x: real): real
  requires x >= 0.0
  ensures sqrt(x) >= 0.0
  ensures sqrt(x) * sqrt(x) == x

// Main method: compute Pearson correlation coefficient between two vectors
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): absolute value for reals */
function absR(x: real): real { if x >= 0.0 then x else -x }

/* helper modified by LLM (iteration 5): non-zero square is positive */
lemma SquarePositive(r: real)
  ensures r != 0.0 ==> r * r > 0.0
{
  if r != 0.0 {
    if r > 0.0 {
      assert r * r > 0.0;
    } else {
      // r < 0.0
      assert r * r > 0.0;
    }
  }
}

/* helper modified by LLM (iteration 5): sqrt of positive is positive */
lemma SqrtPositive(x: real)
  requires x > 0.0
  ensures sqrt(x) > 0.0
{
  var s := sqrt(x);
  // from the specification of sqrt we know s >= 0 and s*s == x
  // s cannot be 0 because then x == 0 contradicts x > 0
  if s == 0.0 {
    assert s * s == 0.0;
    assert x == s * s;
    // contradiction with requires x > 0.0
    assert false;
  }
  // therefore s > 0
}

/* helper modified by LLM (iteration 5): variance positive when sequence has differing elements */
lemma LemmaVariancePositive(values: seq<real>)
  requires |values| > 0
  requires hasNonZeroVariance(values)
  ensures variance(values) > 0.0
{
  var m := mean(values);
  var i, j :| 0 <= i < |values| && 0 <= j < |values| && values[i] != values[j];
  var s := seq(|values|, k requires 0 <= k < |values| => (values[k] - m) * (values[k] - m));
  assert forall k :: 0 <= k < |values| ==> s[k] >= 0.0;
  if values[i] != m {
    // (values[i]-m) != 0 implies its square is > 0
    SquarePositive(values[i] - m);
    assert s[i] > 0.0;
  } else {
    // if values[i] == m then values[j] != m because values[i] != values[j]
    assert values[j] != m;
    SquarePositive(values[j] - m);
    assert s[j] > 0.0;
  }
  // sum of nonnegative numbers with at least one strictly positive element is strictly positive
  // show sum(s) >= s[i or j] and that element > 0
  // pick an index k with s[k] > 0 (established above)
  var k := if values[i] != m then i else j;
  assert s[k] > 0.0;
  // show sum(s) >= s[k]
  // sum(s) == s[k] + sum(other terms) and other terms are >= 0
  var rem := 0.0;
  var idx := 0;
  while idx < |s|
    invariant 0 <= idx <= |s|
    invariant rem == sum(s[0..idx]) - (if 0 <= k < idx then s[k] else 0.0)
  {
    if idx != k {
      rem := rem + s[idx];
    }
    idx := idx + 1;
  }
  // now rem is sum of all s elements except possibly s[k], rem >= 0
  assert rem >= 0.0;
  assert sum(s) == s[k] + rem;
  assert sum(s) > 0.0;
  assert variance(values) == sum(s) / |values| as real;
  assert variance(values) > 0.0;
}

/* helper modified by LLM (iteration 5): Cauchy-Schwarz via choosing optimal scalar */
lemma CauchySchwarzSeq(a: seq<real>, b: seq<real>)
  requires |a| > 0
  requires |a| == |b|
  requires sum(seq(|a|, i requires 0 <= i < |a| => b[i] * b[i])) > 0.0
  ensures (sum(seq(|a|, i requires 0 <= i < |a| => a[i] * b[i]))) * (sum(seq(|a|, i requires 0 <= i < |a| => a[i] * b[i]))) <= (sum(seq(|a|, i requires 0 <= i < |a| => a[i] * a[i]))) * (sum(seq(|a|, i requires 0 <= i < |a| => b[i] * b[i])))
{
  var n := |a|;
  var Saa := sum(seq(n, i requires 0 <= i < n => a[i] * a[i]));
  var Sbb := sum(seq(n, i requires 0 <= i < n => b[i] * b[i]));
  var Sab := sum(seq(n, i requires 0 <= i < n => a[i] * b[i]));
  // choose lambda = Sab / Sbb
  var lambda := Sab / Sbb;
  var t := seq(n, i requires 0 <= i < n => a[i] - lambda * b[i]);
  // sum of squares is non-negative
  var sumt2 := sum(seq(n, i requires 0 <= i < n => t[i] * t[i]));
  assert sumt2 >= 0.0;
  // expand sumt2 using linearity of sum
  assert sumt2 == sum(seq(n, i requires 0 <= i < n => a[i] * a[i])) - 2.0 * lambda * sum(seq(n, i requires 0 <= i < n => a[i] * b[i])) + lambda * lambda * sum(seq(n, i requires 0 <= i < n => b[i] * b[i]));
  assert sumt2 == Saa - 2.0 * lambda * Sab + lambda * lambda * Sbb;
  // substitute lambda = Sab / Sbb
  assert sumt2 == Saa - 2.0 * (Sab / Sbb) * Sab + (Sab / Sbb) * (Sab / Sbb) * Sbb;
  // simplify to Saa - Sab*Sab / Sbb
  assert sumt2 == Saa - (Sab * Sab) / Sbb;
  assert sumt2 >= 0.0;
  // multiply by Sbb > 0 to obtain Sbb*Saa - Sab*Sab >= 0
  assert Sbb > 0.0;
  assert Sbb * (Saa - (Sab * Sab) / Sbb) >= 0.0;
  assert Sbb * Saa - Sab * Sab >= 0.0;
  assert Sab * Sab <= Saa * Sbb;
}

/* helper modified by LLM (iteration 5): covariance bound via Cauchy-Schwarz */
lemma CovarianceBound(x: seq<real>, y: seq<real>)
  requires |x| > 0
  requires |x| == |y|
  requires variance(x) > 0.0
  requires variance(y) > 0.0
  ensures absR(covariance(x, y)) <= standardDeviation(x) * standardDeviation(y)
{
  var n := |x|;
  var mx := mean(x);
  var my := mean(y);
  var a := seq(n, i requires 0 <= i < n => x[i] - mx);
  var b := seq(n, i requires 0 <= i < n => y[i] - my);
  var Sab := sum(seq(n, i requires 0 <= i < n => a[i] * b[i]));
  var Saa := sum(seq(n, i requires 0 <= i < n => a[i] * a[i]));
  var Sbb := sum(seq(n, i requires 0 <= i < n => b[i] * b[i]));
  assert Sab == (n as real) * covariance(x, y);
  assert Saa == (n as real) * variance(x);
  assert Sbb == (n as real) * variance(y);
  assert Sbb > 0.0;
  // apply Cauchy-Schwarz to sequences a and b
  CauchySchwarzSeq(a, b);
  assert Sab * Sab <= Saa * Sbb;
  // convert sum-based inequality to function-based inequality
  assert (Sab / (n as real)) * (Sab / (n as real)) <= (Saa / (n as real)) * (Sbb / (n as real));
  assert covariance(x, y) * covariance(x, y) <= variance(x) * variance(y);

  var sd_x := standardDeviation(x);
  var sd_y := standardDeviation(y);
  // relate squares
  assert sd_x * sd_x == variance(x);
  assert sd_y * sd_y == variance(y);
  assert (sd_x * sd_y) * (sd_x * sd_y) == variance(x) * variance(y);

  var cov := covariance(x, y);
  var sprod := sd_x * sd_y;
  assert (cov * cov) <= (sprod * sprod);
  if cov >= 0.0 {
    if cov > sprod {
      assert cov * cov > sprod * sprod;
      // contradiction
      assert false;
    }
    assert cov <= sprod;
  } else {
    var ncov := -cov;
    if ncov > sprod {
      assert ncov * ncov > sprod * sprod;
      // contradiction
      assert false;
    }
    assert -cov <= sprod;
  }
  assert absR(cov) <= sprod;
}

/* helper modified by LLM (iteration 5): covariance symmetric */
lemma CovarianceSymmetry(x: seq<real>, y: seq<real>)
  requires |x| > 0
  requires |x| == |y|
  ensures covariance(x, y) == covariance(y, x)
{
  var n := |x|;
  var mx := mean(x);
  var my := mean(y);
  var s1 := seq(n, i requires 0 <= i < n => (x[i] - mx) * (y[i] - my));
  var s2 := seq(n, i requires 0 <= i < n => (y[i] - my) * (x[i] - mx));
  assert s1 == s2;
  assert sum(s1) == sum(s2);
  assert covariance(x, y) == sum(s1) / n as real;
  assert covariance(y, x) == sum(s2) / n as real;
  assert covariance(x, y) == covariance(y, x);
}

// </vc-helpers>

// <vc-spec>
method corrcoef(x: seq<real>, y: seq<real>) returns (result: real)
  // Vectors must be non-empty and of equal length
  requires |x| > 0
  requires |y| > 0
  requires |x| == |y|
  
  // Both vectors must have non-zero variance (not all elements equal)
  requires hasNonZeroVariance(x)
  requires hasNonZeroVariance(y)
  
  // Correlation coefficient is bounded between -1 and 1
  ensures -1.0 <= result <= 1.0
  
  // Correlation coefficient equals covariance normalized by product of standard deviations
  ensures variance(x) > 0.0 && variance(y) > 0.0
  ensures result == covariance(x, y) / (standardDeviation(x) * standardDeviation(y))
  
  // Symmetry property: corr(x, y) == corr(y, x)
  ensures result == covariance(y, x) / (standardDeviation(y) * standardDeviation(x))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): compute Pearson correlation using covariance and stddev */
{
  // prove variances positive so standardDeviation can be called
  LemmaVariancePositive(x);
  LemmaVariancePositive(y);
  // compute standard deviations
  var sd_x := standardDeviation(x);
  var sd_y := standardDeviation(y);
  // establish they are strictly positive
  SqrtPositive(variance(x));
  SqrtPositive(variance(y));
  // compute covariance and apply bound
  var cov := covariance(x, y);
  CovarianceBound(x, y);
  // numerator and denominator
  var denom := sd_x * sd_y;
  assert denom > 0.0;
  // form result and prove bounds
  if cov >= 0.0 {
    assert cov <= denom;
    result := cov / denom;
    assert result <= 1.0;
  } else {
    assert -cov <= denom;
    result := cov / denom;
    assert -result <= 1.0;
  }
  // ensure equality and symmetry postconditions
  assert result == covariance(x, y) / (sd_x * sd_y);
  assert result == covariance(y, x) / (sd_y * sd_x);
  assert -1.0 <= result && result <= 1.0;
}

// </vc-code>
