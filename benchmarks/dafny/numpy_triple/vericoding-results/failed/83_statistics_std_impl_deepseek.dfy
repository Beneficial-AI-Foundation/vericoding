// <vc-preamble>
/*
 * Standard deviation computation following NumPy's std function specification.
 * Computes the standard deviation of array elements using the formula:
 * std = sqrt(sum((x_i - mean)²) / (N - ddof))
 * where ddof is the "Delta Degrees of Freedom" parameter.
 */

// Helper function to compute sum of a sequence
ghost function Sum(s: seq<real>): real
{
    if |s| == 0 then 0.0
    else s[0] + Sum(s[1..])
}

// Helper function to compute mean of a non-empty sequence
ghost function Mean(s: seq<real>): real
    requires |s| > 0
{
    Sum(s) / (|s| as real)
}

// Helper function to compute squared deviations from mean
ghost function SquaredDeviations(s: seq<real>, mean: real): seq<real>
{
    seq(|s|, i requires 0 <= i < |s| => (s[i] - mean) * (s[i] - mean))
}

// Helper function to compute variance
ghost function Variance(s: seq<real>, ddof: nat): real
    requires |s| > 0
    requires ddof < |s|
{
    var mean := Mean(s);
    var squared_devs := SquaredDeviations(s, mean);
    Sum(squared_devs) / ((|s| - ddof) as real)
}

// Main standard deviation computation method
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fix Sqrt function to properly handle square root computation and verification */
function Sqrt(x: real): real
  requires x >= 0.0
  ensures Sqrt(x) >= 0.0
  ensures Sqrt(x) * Sqrt(x) == x
{
  if x == 0.0 then 0.0 else
  var y := x / 2.0;
  var prev := 0.0;
  while y != prev
    invariant y >= 0.0
    invariant y * y <= x
    decreases if y >= prev then y - prev else prev - y
  {
    prev := y;
    y := (y + x / y) / 2.0;
  }
  y
}

/* helper modified by LLM (iteration 5): Add lemma to connect ComputeSum and Sum functions */
lemma ComputeSumEqualsSum(s: seq<real>)
  ensures ComputeSum(s) == Sum(s)
{
}

/* helper modified by LLM (iteration 5): Add lemma to connect ComputeMean and Mean functions */
lemma ComputeMeanEqualsMean(s: seq<real>)
  requires |s| > 0
  ensures ComputeMean(s) == Mean(s)
{
  ComputeSumEqualsSum(s);
}

/* helper modified by LLM (iteration 5): Add lemma to connect ComputeSquaredDeviations and SquaredDeviations functions */
lemma ComputeSquaredDeviationsEqualsSquaredDeviations(s: seq<real>, mean: real)
  ensures ComputeSquaredDeviations(s, mean) == SquaredDeviations(s, mean)
{
}

/* helper modified by LLM (iteration 5): Add lemma to connect ComputeVariance and Variance functions */
lemma ComputeVarianceEqualsVariance(s: seq<real>, ddof: nat)
  requires |s| > 0
  requires ddof < |s|
  ensures ComputeVariance(s, ddof) == Variance(s, ddof)
{
  ComputeMeanEqualsMean(s);
  ComputeSquaredDeviationsEqualsSquaredDeviations(s, ComputeMean(s));
  ComputeSumEqualsSum(ComputeSquaredDeviations(s, ComputeMean(s)));
}
// </vc-helpers>

// <vc-spec>
method numpy_std(a: seq<real>, ddof: nat := 0) returns (result: real)
    requires |a| > 0  // Non-empty sequence
    requires ddof < |a|  // ddof must be less than number of elements
    ensures result >= 0.0  // Standard deviation is always non-negative
    ensures (|a| - ddof) > 0  // Explicit denominator positivity
    ensures result * result == Variance(a, ddof)  // Core computational specification
    ensures var mean := Mean(a);
            (forall i :: 0 <= i < |a| ==> a[i] == mean) ==> result == 0.0
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Fix loop invariant and add proper verification */
  var mean := ComputeMean(a);
  var sq_sum := 0.0;
  var i := 0;
  
  while i < |a|
    invariant 0 <= i <= |a|
    invariant sq_sum == ComputeSum(ComputeSquaredDeviations(a[0..i], mean))
  {
    var deviation := a[i] - mean;
    sq_sum := sq_sum + deviation * deviation;
    i := i + 1;
  }
  
  ComputeSumEqualsSum(ComputeSquaredDeviations(a, mean));
  ComputeVarianceEqualsVariance(a, ddof);
  assert sq_sum == ComputeSum(ComputeSquaredDeviations(a, mean));
  assert sq_sum == Sum(SquaredDeviations(a, Mean(a)));
  assert Variance(a, ddof) == sq_sum / ((|a| - ddof) as real);
  
  result := Sqrt(sq_sum / ((|a| - ddof) as real));
  
  // Postcondition: all elements equal to mean implies result is 0
  if forall i :: 0 <= i < |a| ==> a[i] == mean {
    assert sq_sum == 0.0;
    assert result == 0.0;
  }
}
// </vc-code>
