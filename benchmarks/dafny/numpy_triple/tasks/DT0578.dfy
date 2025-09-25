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
  assume {:axiom} false;
}
// </vc-code>
