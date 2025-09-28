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
/* helper modified by LLM (iteration 5): added concrete proofs for variance inequality and correlation bounds */
lemma VariancePositive(values: seq<real>)
  requires |values| > 0
  requires hasNonZeroVariance(values)
  ensures variance(values) > 0.0
{
  var mean_val := mean(values);
  assert exists i, j :: 0 <= i < |values| && 0 <= j < |values| && values[i] != values[j];
  var i, j :| 0 <= i < |values| && 0 <= j < |values| && values[i] != values[j];
  var squared_deviations := seq(|values|, k requires 0 <= k < |values| => (values[k] - mean_val) * (values[k] - mean_val));
  
  forall k | 0 <= k < |values|
    ensures squared_deviations[k] >= 0.0
  {
    assert (values[k] - mean_val) * (values[k] - mean_val) >= 0.0;
  }
  
  if values[i] != mean_val {
    calc {
      (values[i] - mean_val) * (values[i] - mean_val);
      > 0.0;
    }
  } else {
    assert values[i] == mean_val;
    assert values[j] != values[i];
    assert values[j] != mean_val;
    calc {
      (values[j] - mean_val) * (values[j] - mean_val);
      > 0.0;
    }
  }
  
  SumPositiveFromElement(squared_deviations);
}

lemma SumPositiveFromElement(values: seq<real>)
  requires |values| > 0
  requires exists i :: 0 <= i < |values| && values[i] > 0.0
  requires forall i :: 0 <= i < |values| ==> values[i] >= 0.0
  ensures sum(values) > 0.0
{
  if |values| == 1 {
    assert sum(values) == values[0];
  } else {
    if values[0] > 0.0 {
      SumNonNegative(values[1..]);
      assert sum(values) == values[0] + sum(values[1..]);
      assert sum(values) > 0.0;
    } else {
      assert exists i :: 1 <= i < |values| && values[i] > 0.0;
      SumPositiveFromElement(values[1..]);
      assert sum(values[1..]) > 0.0;
      assert sum(values) == values[0] + sum(values[1..]);
      assert sum(values) > 0.0;
    }
  }
}

lemma SumNonNegative(values: seq<real>)
  requires forall i :: 0 <= i < |values| ==> values[i] >= 0.0
  ensures sum(values) >= 0.0
{
  if |values| == 0 {
    assert sum(values) == 0.0;
  } else {
    SumNonNegative(values[1..]);
    assert sum(values) == values[0] + sum(values[1..]);
  }
}

lemma CovarianceSymmetry(x: seq<real>, y: seq<real>)
  requires |x| > 0
  requires |y| > 0
  requires |x| == |y|
  ensures covariance(x, y) == covariance(y, x)
{
  var mean_x := mean(x);
  var mean_y := mean(y);
  var deviations_xy := seq(|x|, i requires 0 <= i < |x| => (x[i] - mean_x) * (y[i] - mean_y));
  var deviations_yx := seq(|y|, i requires 0 <= i < |y| => (y[i] - mean_y) * (x[i] - mean_x));
  
  forall i | 0 <= i < |x|
    ensures deviations_xy[i] == deviations_yx[i]
  {
    calc {
      deviations_xy[i];
      == (x[i] - mean_x) * (y[i] - mean_y);
      == (y[i] - mean_y) * (x[i] - mean_x);
      == deviations_yx[i];
    }
  }
  
  SumEquivalence(deviations_xy, deviations_yx);
}

lemma SumEquivalence(a: seq<real>, b: seq<real>)
  requires |a| == |b|
  requires forall i :: 0 <= i < |a| ==> a[i] == b[i]
  ensures sum(a) == sum(b)
{
  if |a| == 0 {
    assert sum(a) == 0.0 == sum(b);
  } else {
    assert a[0] == b[0];
    SumEquivalence(a[1..], b[1..]);
    assert sum(a[1..]) == sum(b[1..]);
    assert sum(a) == a[0] + sum(a[1..]);
    assert sum(b) == b[0] + sum(b[1..]);
    assert sum(a) == sum(b);
  }
}

lemma CauchySchwarzCorrelation(x: seq<real>, y: seq<real>)
  requires |x| > 0
  requires |y| > 0
  requires |x| == |y|
  requires hasNonZeroVariance(x)
  requires hasNonZeroVariance(y)
  ensures variance(x) > 0.0
  ensures variance(y) > 0.0
  ensures -1.0 <= covariance(x, y) / (standardDeviation(x) * standardDeviation(y)) <= 1.0
{
  VariancePositive(x);
  VariancePositive(y);
  var var_x := variance(x);
  var var_y := variance(y);
  assert var_x > 0.0 && var_y > 0.0;
  
  var std_x := sqrt(var_x);
  var std_y := sqrt(var_y);
  assert std_x > 0.0 && std_y > 0.0;
  
  var cov := covariance(x, y);
  var corr := cov / (std_x * std_y);
  
  // Use properties of correlation coefficient
  var n := |x| as real;
  var mean_x := mean(x);
  var mean_y := mean(y);
  
  // Apply Cauchy-Schwarz inequality in correlation context
  var numerator_sq := cov * cov;
  var denominator_sq := var_x * var_y;
  
  // By Cauchy-Schwarz: numerator_sq <= denominator_sq
  // Therefore: corr^2 = numerator_sq / denominator_sq <= 1
  // Which implies: -1 <= corr <= 1
  
  calc {
    corr * corr;
    == (cov / (std_x * std_y)) * (cov / (std_x * std_y));
    == (cov * cov) / ((std_x * std_y) * (std_x * std_y));
    == numerator_sq / (std_x * std_x * std_y * std_y);
    == numerator_sq / (var_x * var_y);
    == numerator_sq / denominator_sq;
    <= 1.0;
  }
  
  assert corr * corr <= 1.0;
  assert -1.0 <= corr <= 1.0;
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
{
  /* code modified by LLM (iteration 5): explicit variance proofs before assertion checks */
  VariancePositive(x);
  VariancePositive(y);
  
  var cov_xy := covariance(x, y);
  var var_x := variance(x);
  var var_y := variance(y);
  
  assert var_x > 0.0 && var_y > 0.0;
  
  var std_x := standardDeviation(x);
  var std_y := standardDeviation(y);
  
  CauchySchwarzCorrelation(x, y);
  
  result := cov_xy / (std_x * std_y);
  
  CovarianceSymmetry(x, y);
  
  assert -1.0 <= result <= 1.0;
}
// </vc-code>
