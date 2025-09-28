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
/* helper modified by LLM (iteration 5): implementing non-ghost SquareRoot function */
function method SquareRoot(x: real): real
    requires x >= 0.0
    ensures SquareRoot(x) >= 0.0
    ensures SquareRoot(x) * SquareRoot(x) == x
{
    if x == 0.0 then 0.0
    else
        var guess := x / 2.0;
        NewtonSqrt(x, guess, 10)
}

function method NewtonSqrt(x: real, guess: real, iterations: nat): real
    requires x >= 0.0
    requires guess > 0.0 || x == 0.0
    decreases iterations
{
    if iterations == 0 then guess
    else
        var newGuess := (guess + x / guess) / 2.0;
        NewtonSqrt(x, newGuess, iterations - 1)
}

function method ComputeSumSquaredDeviations(s: seq<real>, mean: real): real
{
    if |s| == 0 then 0.0
    else (s[0] - mean) * (s[0] - mean) + ComputeSumSquaredDeviations(s[1..], mean)
}

function method ComputeSum(s: seq<real>): real
{
    if |s| == 0 then 0.0
    else s[0] + ComputeSum(s[1..])
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
  /* code modified by LLM (iteration 5): use non-ghost functions for computation */
  var mean := ComputeSum(a) / (|a| as real);
  var sumSquaredDevs := ComputeSumSquaredDeviations(a, mean);
  var variance := sumSquaredDevs / ((|a| - ddof) as real);
  result := SquareRoot(variance);
}
// </vc-code>
