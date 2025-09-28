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
/* helper modified by LLM (iteration 5): prove non-negativity of sum of squares */
lemma NonNegSumOfSquares(s: seq<real>)
  ensures Sum(seq(|s|, i => s[i] * s[i])) >= 0.0
  decreases |s|
{
  if |s| == 0 {
  } else {
    var t := s[1..];
    NonNegSumOfSquares(t);
    assert Sum(seq(|s|, i => s[i] * s[i])) == s[0] * s[0] + Sum(seq(|t|, i => t[i] * t[i]));
    assert s[0] * s[0] >= 0.0;
    assert Sum(seq(|t|, i => t[i] * t[i])) >= 0.0;
  }
}

/* helper modified by LLM (iteration 5): sum when all elements equal */
lemma SumAllEqual(s: seq<real>)
  requires |s| > 0
  ensures (forall i :: 0 <= i < |s| ==> s[i] == s[0]) ==> Sum(s) == (|s| as real) * s[0]
  decreases |s|
{
  if |s| == 1 {
    // Sum of single-element sequence is that element
    assert Sum(s) == s[0];
    if forall i :: 0 <= i < |s| ==> s[i] == s[0] {
      assert Sum(s) == (|s| as real) * s[0];
    }
  } else {
    var t := s[1..];
    SumAllEqual(t);
    if forall i :: 0 <= i < |s| ==> s[i] == s[0] {
      assert Sum(s) == s[0] + Sum(t);
      assert Sum(t) == (|t| as real) * s[0];
      assert Sum(s) == (|s| as real) * s[0];
    }
  }
}

/* helper modified by LLM (iteration 5): sum of squared deviations is non-negative */
lemma SumSquaredDeviationsNonNeg(s: seq<real>)
  requires |s| > 0
  ensures Sum(SquaredDeviations(s, Mean(s))) >= 0.0
  decreases |s|
{
  var mean := Mean(s);
  var devs := seq(|s|, i => s[i] - mean);
  NonNegSumOfSquares(devs);
  assert forall i :: 0 <= i < |s| ==> SquaredDeviations(s, mean)[i] == devs[i] * devs[i];
  assert Sum(SquaredDeviations(s, mean)) == Sum(seq(|s|, i => devs[i] * devs[i]));
  // From NonNegSumOfSquares we get the non-negativity
  assert Sum(SquaredDeviations(s, mean)) >= 0.0;
}

/* helper modified by LLM (iteration 5): zero variance when all elements equal */
lemma AllEqualZeroVariance(s: seq<real>)
  requires |s| > 0
  ensures (forall i :: 0 <= i < |s| ==> s[i] == s[0]) ==> Sum(SquaredDeviations(s, Mean(s))) == 0.0
  decreases |s|
{
  if forall i :: 0 <= i < |s| ==> s[i] == s[0] {
    SumAllEqual(s);
    assert Mean(s) == s[0];
    assert forall i :: 0 <= i < |s| ==> SquaredDeviations(s, Mean(s))[i] == 0.0;
    assert Sum(SquaredDeviations(s, Mean(s))) == 0.0;
  }
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
/* code modified by LLM (iteration 5): compute std via variance and non-deterministic sqrt witness */
{
  var m := Mean(a);
  SumSquaredDeviationsNonNeg(a);
  assert Sum(SquaredDeviations(a, m)) >= 0.0;
  assert (|a| - ddof) > 0;
  var v := Sum(SquaredDeviations(a, m)) / ((|a| - ddof) as real);
  assert v == Variance(a, ddof);
  assert v >= 0.0;
  var r: real :| r * r == v && r >= 0.0;
  result := r;
  assert result >= 0.0;
  assert result * result == v;
  // If all elements equal, variance is zero, so the non-deterministic choice must be 0
  if forall i :: 0 <= i < |a| ==> a[i] == m {
    AllEqualZeroVariance(a);
    assert Sum(SquaredDeviations(a, m)) == 0.0;
    assert v == 0.0;
    assert result == 0.0;
  }
}
// </vc-code>
