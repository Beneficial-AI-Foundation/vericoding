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
/* helper modified by LLM (iteration 5): Non-negativity of sum of non-negative sequence */
lemma SumNonNegative(s: seq<real>)
  requires forall i :: 0 <= i < |s| ==> s[i] >= 0.0
  ensures Sum(s) >= 0.0
  decreases |s|
{
  if |s| == 0 {
  } else {
    SumNonNegative(s[1..]);
    assert Sum(s) == s[0] + Sum(s[1..]);
    assert s[0] >= 0.0;
    assert Sum(s[1..]) >= 0.0;
    assert s[0] + Sum(s[1..]) >= 0.0;
  }
}

/* helper modified by LLM (iteration 5): Non-negativity of squared deviations via pointwise reasoning */
lemma SquaredDeviationsNonNeg(s: seq<real>, m: real)
  ensures forall i :: 0 <= i < |SquaredDeviations(s, m)| ==> SquaredDeviations(s, m)[i] >= 0.0
{
  assert |SquaredDeviations(s, m)| == |s|;
  forall i | 0 <= i < |SquaredDeviations(s, m)| {
    assert |SquaredDeviations(s, m)| == |s|;
    assert 0 <= i < |s|;
    assert SquaredDeviations(s, m)[i] == (s[i] - m) * (s[i] - m);
    assert (s[i] - m) * (s[i] - m) >= 0.0;
  }
}

/* helper modified by LLM (iteration 5): Variance is non-negative given ddof < |s| */
lemma VarianceNonNeg(s: seq<real>, ddof: nat)
  requires |s| > 0
  requires ddof < |s|
  ensures Variance(s, ddof) >= 0.0
{
  var m := Mean(s);
  SquaredDeviationsNonNeg(s, m);
  SumNonNegative(SquaredDeviations(s, m));
  var den := (|s| - ddof) as real;
  assert den > 0.0;
  assert Variance(s, ddof) == Sum(SquaredDeviations(s, m)) / den;
  assert Sum(SquaredDeviations(s, m)) >= 0.0;
  assert Sum(SquaredDeviations(s, m)) / den >= 0.0;
}

/* helper modified by LLM (iteration 5): Sum equals zero when all elements are zero */
lemma SumZeroIfAllZero(s: seq<real>)
  ensures (forall i :: 0 <= i < |s| ==> s[i] == 0.0) ==> Sum(s) == 0.0
  decreases |s|
{
  if |s| == 0 {
  } else {
    if (forall i :: 0 <= i < |s| ==> s[i] == 0.0) {
      assert |s[1..]| == |s| - 1;
      assert forall i :: 0 <= i < |s[1..]| ==> s[1..][i] == 0.0 by {
        forall i | 0 <= i < |s[1..]| {
          assert |s[1..]| == |s| - 1;
          assert 0 <= i < |s| - 1;
          assert 0 <= i + 1 < |s|;
          assert s[i + 1] == 0.0;
          assert s[1..][i] == s[i + 1];
        }
      }
      SumZeroIfAllZero(s[1..]);
      assert Sum(s) == s[0] + Sum(s[1..]);
      assert s[0] == 0.0;
      assert Sum(s[1..]) == 0.0;
      assert Sum(s) == 0.0;
    } else {
      // Implication holds vacuously
    }
  }
}

/* helper modified by LLM (iteration 5): Variance is zero if all elements equal the mean */
lemma VarianceZeroIfAllEqual(s: seq<real>, ddof: nat)
  requires |s| > 0
  requires ddof < |s|
  ensures (forall i :: 0 <= i < |s| ==> s[i] == Mean(s)) ==> Variance(s, ddof) == 0.0
{
  var m := Mean(s);
  if (forall i :: 0 <= i < |s| ==> s[i] == m) {
    assert forall i :: 0 <= i < |s| ==> SquaredDeviations(s, m)[i] == 0.0 by {
      forall i | 0 <= i < |s| {
        assert s[i] == m;
        assert SquaredDeviations(s, m)[i] == (s[i] - m) * (s[i] - m);
        assert (s[i] - m) == 0.0;
        assert (s[i] - m) * (s[i] - m) == 0.0;
      }
    }
    var sd := SquaredDeviations(s, m);
    SumZeroIfAllZero(sd);
    assert Sum(sd) == 0.0;
    var den := (|s| - ddof) as real;
    assert den > 0.0;
    assert Variance(s, ddof) == Sum(sd) / den;
    assert Variance(s, ddof) == 0.0;
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
{
  /* code modified by LLM (iteration 5): direct use of ghost variance and square-root choice without invalid ghost assignments */
  // Preconditions imply positive denominator
  assert |a| > 0;
  assert ddof < |a|;
  assert (|a| - ddof) > 0;

  // Variance is non-negative
  VarianceNonNeg(a, ddof);
  ghost var v := Variance(a, ddof);
  assert v >= 0.0;

  // Choose a non-negative square root of v
  var r: real :| r >= 0.0 && r * r == v;
  result := r;

  // Connect result to specification
  assert result * result == Variance(a, ddof);
  assert result >= 0.0;

  // If all elements equal the mean, variance is zero, hence result is zero
  if (forall i :: 0 <= i < |a| ==> a[i] == Mean(a)) {
    VarianceZeroIfAllEqual(a, ddof);
    assert Variance(a, ddof) == 0.0;
    assert result == 0.0;
  }
}
// </vc-code>
