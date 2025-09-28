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
/* helper modified by LLM (iteration 4): Strengthen variance bounds and correlation lemmas with detailed proofs */
lemma hasNonZeroVarianceImpliesPositiveVariance(values: seq<real>)
  requires |values| > 0
  requires hasNonZeroVariance(values)
  ensures variance(values) > 0.0
{
  var mean_val := mean(values);
  // Since hasNonZeroVariance holds, there exist i, j with values[i] != values[j]
  var i, j :| 0 <= i < |values| && 0 <= j < |values| && values[i] != values[j];
  
  // At least one of values[i] or values[j] must differ from the mean
  if values[i] != mean_val {
    var diff_i := values[i] - mean_val;
    assert diff_i != 0.0;
    var dev_i := diff_i * diff_i;
    assert dev_i > 0.0;
    
    // The sum of squared deviations includes dev_i, so it's at least dev_i
    var squared_deviations := seq(|values|, k requires 0 <= k < |values| => (values[k] - mean_val) * (values[k] - mean_val));
    assert squared_deviations[i] == dev_i;
    // All squared deviations are non-negative, so sum is at least dev_i
    assert sum(squared_deviations) >= dev_i;
    
    // Since dev_i > 0 and |values| > 0, variance is positive
    assert variance(values) == sum(squared_deviations) / |values| as real;
    assert variance(values) > 0.0;
  } else if values[j] != mean_val {
    var diff_j := values[j] - mean_val;
    assert diff_j != 0.0;
    var dev_j := diff_j * diff_j;
    assert dev_j > 0.0;
    
    var squared_deviations := seq(|values|, k requires 0 <= k < |values| => (values[k] - mean_val) * (values[k] - mean_val));
    assert squared_deviations[j] == dev_j;
    // All squared deviations are non-negative, so sum is at least dev_j
    assert sum(squared_deviations) >= dev_j;
    
    assert variance(values) == sum(squared_deviations) / |values| as real;
    assert variance(values) > 0.0;
  } else {
    // Both values[i] and values[j] equal mean_val, but values[i] != values[j] - contradiction
    assert false;
  }
}

lemma correlationBounds(x: seq<real>, y: seq<real>)
  requires |x| > 0
  requires |y| > 0
  requires |x| == |y|
  requires hasNonZeroVariance(x)
  requires hasNonZeroVariance(y)
  ensures -1.0 <= covariance(x, y) / (standardDeviation(x) * standardDeviation(y)) <= 1.0
{
  hasNonZeroVarianceImpliesPositiveVariance(x);
  hasNonZeroVarianceImpliesPositiveVariance(y);
  
  var n := |x| as real;
  var mean_x := mean(x);
  var mean_y := mean(y);
  
  // Define normalized deviations
  var x_dev := seq(|x|, i requires 0 <= i < |x| => x[i] - mean_x);
  var y_dev := seq(|y|, i requires 0 <= i < |y| => y[i] - mean_y);
  
  // Correlation formula in terms of normalized deviations
  var numerator := sum(seq(|x|, i requires 0 <= i < |x| => x_dev[i] * y_dev[i])) / n;
  var denom_x := sum(seq(|x|, i requires 0 <= i < |x| => x_dev[i] * x_dev[i])) / n;
  var denom_y := sum(seq(|y|, i requires 0 <= i < |y| => y_dev[i] * y_dev[i])) / n;
  
  // Since variance is positive, denom_x and denom_y are positive
  assert denom_x > 0.0;
  assert denom_y > 0.0;
  
  // By Cauchy-Schwarz inequality: (sum a_i * b_i)^2 <= (sum a_i^2) * (sum b_i^2)
  // This implies |correlation| <= 1
  assert numerator * numerator <= denom_x * denom_y;
  
  // Since denom_x and denom_y are positive, we can take square roots
  assert sqrt(denom_x) > 0.0;
  assert sqrt(denom_y) > 0.0;
  
  var corr := numerator / (sqrt(denom_x) * sqrt(denom_y));
  assert -1.0 <= corr <= 1.0;
}

lemma covarianceSymmetry(x: seq<real>, y: seq<real>)
  requires |x| > 0
  requires |y| > 0
  requires |x| == |y|
  ensures covariance(x, y) == covariance(y, x)
{
  var mean_x := mean(x);
  var mean_y := mean(y);
  
  var deviations_xy := seq(|x|, i requires 0 <= i < |x| => (x[i] - mean_x) * (y[i] - mean_y));
  var deviations_yx := seq(|y|, i requires 0 <= i < |y| => (y[i] - mean_y) * (x[i] - mean_x));
  
  // For each i, (x[i] - mean_x) * (y[i] - mean_y) = (y[i] - mean_y) * (x[i] - mean_x)
  forall i | 0 <= i < |x| {
    assert deviations_xy[i] == deviations_yx[i];
  }
  
  // Therefore the sums are equal
  assert sum(deviations_xy) == sum(deviations_yx);
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
  /* code modified by LLM (iteration 4): Compute correlation coefficient with proper variance proofs */
  // First prove that both sequences have positive variance
  hasNonZeroVarianceImpliesPositiveVariance(x);
  hasNonZeroVarianceImpliesPositiveVariance(y);
  
  // Prove the correlation bounds and symmetry properties
  correlationBounds(x, y);
  covarianceSymmetry(x, y);
  
  // Now compute the correlation coefficient
  result := covariance(x, y) / (standardDeviation(x) * standardDeviation(y));
}
// </vc-code>
