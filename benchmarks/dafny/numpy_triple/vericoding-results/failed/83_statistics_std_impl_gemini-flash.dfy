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
/* code modified by LLM (iteration 5): Fix compilation error with `real.sqrt`. */
{
    var mean_val := Mean(a);
    var sum_squared_deviations := 0.0;
    var i := 0;
    while i < |a|
        invariant 0 <= i <= |a|
        invariant sum_squared_deviations == Sum(SquaredDeviations(a, mean_val)[0..i])
        decreases |a| - i
    {
        sum_squared_deviations := sum_squared_deviations + (a[i] - mean_val) * (a[i] - mean_val);
        i := i + 1;
    }
    var N_minus_ddof_real := (|a| - ddof) as real;
    // Since sum_squared_deviations >= 0 and N_minus_ddof_real > 0, variance_val will be >= 0.
    var variance_val := sum_squared_deviations / N_minus_ddof_real;
    result := real.sqrt(variance_val);
}
// </vc-code>
