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
/* helper modified by LLM (iteration 5): added assertions to guide proof */
lemma SumAppend(s1: seq<real>, s2: seq<real>)
    ensures Sum(s1 + s2) == Sum(s1) + Sum(s2)
    decreases |s1|
{
    if |s1| > 0 {
        SumAppend(s1[1..], s2);
        assert Sum(s1) == s1[0] + Sum(s1[1..]);
        assert Sum(s1 + s2) == s1[0] + Sum(s1[1..] + s2);
    }
}

/* helper modified by LLM (iteration 2): added lemma about non-negativity of squares */
lemma SquareNonNegative(x: real)
    ensures x * x >= 0.0
{
}

/* helper modified by LLM (iteration 5): added assertions to guide proof */
lemma SumIsNonNegative(s: seq<real>)
    requires forall i :: 0 <= i < |s| ==> s[i] >= 0.0
    ensures Sum(s) >= 0.0
    decreases |s|
{
    if |s| > 0 {
        SumIsNonNegative(s[1..]);
        assert Sum(s) == s[0] + Sum(s[1..]);
    }
}

/* helper modified by LLM (iteration 5): added assertions to guide proof */
lemma SumIsZero(s: seq<real>)
    requires forall i :: 0 <= i < |s| ==> s[i] == 0.0
    ensures Sum(s) == 0.0
    decreases |s|
{
    if |s| > 0 {
        SumIsZero(s[1..]);
        assert Sum(s) == s[0] + Sum(s[1..]);
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
    /* code modified by LLM (iteration 5): added lemma calls to prove loop invariants */
    // Step 1: Compute sum of elements
    var current_sum: real := 0.0;
    var i := 0;
    while i < |a|
        invariant 0 <= i <= |a|
        invariant current_sum == Sum(a[..i])
    {
        SumAppend(a[..i], [a[i]]);
        current_sum := current_sum + a[i];
        i := i + 1;
    }

    // Step 2: Compute mean
    var mean := current_sum / (|a| as real);
    assert mean == Mean(a);

    // Step 3: Compute sum of squared deviations
    ghost var s_devs := SquaredDeviations(a, mean);
    var sum_sq_dev: real := 0.0;
    i := 0;
    while i < |a|
        invariant 0 <= i <= |a|
        invariant sum_sq_dev == Sum(s_devs[..i])
    {
        var dev := a[i] - mean;
        assert s_devs[i] == dev * dev;
        SumAppend(s_devs[..i], [s_devs[i]]);
        sum_sq_dev := sum_sq_dev + dev * dev;
        i := i + 1;
    }
    assert sum_sq_dev == Sum(s_devs);

    // Step 4: Compute variance
    var variance_val := sum_sq_dev / ((|a| - ddof) as real);
    assert variance_val == Variance(a, ddof);

    // Step 5: Compute square root using a non-constructive choice.
    forall k | 0 <= k < |s_devs|
        ensures s_devs[k] >= 0.0
    {
        SquareNonNegative(a[k] - mean);
    }
    SumIsNonNegative(s_devs);
    assert sum_sq_dev >= 0.0;
    assert variance_val >= 0.0;

    var r :| r >= 0.0 && r * r == variance_val;
    result := r;

    // Prove conditional postcondition
    if forall i :: 0 <= i < |a| ==> a[i] == mean {
        assert forall i | 0 <= i < |s_devs| :: s_devs[i] == 0.0;
        SumIsZero(s_devs);
        assert sum_sq_dev == 0.0;
        assert variance_val == 0.0;
        assert result == 0.0;
    }
}
// </vc-code>
