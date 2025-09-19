// <vc-preamble>
// Datatype to represent floating point values that can be NaN
datatype FloatValue = RealVal(val: real) | NaN

// Predicate to check if a FloatValue is NaN
predicate IsNaN(f: FloatValue)
{
    f.NaN?
}

// Extract real value from FloatValue (only valid for non-NaN values)
function GetRealValue(f: FloatValue): real
    requires !IsNaN(f)
{
    f.val
}

// Filter out NaN values and return sequence of real values
function FilterValidValues(a: seq<FloatValue>): seq<real>
{
    if |a| == 0 then []
    else if IsNaN(a[0]) then FilterValidValues(a[1..])
    else [GetRealValue(a[0])] + FilterValidValues(a[1..])
}

// Sum a sequence of real values
function Sum(values: seq<real>): real
{
    if |values| == 0 then 0.0
    else values[0] + Sum(values[1..])
}

// Calculate mean of a sequence of real values
function Mean(values: seq<real>): real
    requires |values| > 0
{
    Sum(values) / |values| as real
}

// Calculate sum of squared deviations from mean
function SumSquaredDeviations(values: seq<real>, mean: real): real
{
    Sum(seq(|values|, i => (values[i] - mean) * (values[i] - mean)))
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method nanvar(a: seq<FloatValue>, ddof: nat) returns (result: FloatValue)
    ensures var validValues := FilterValidValues(a);
            var validCount := |validValues|;
            if validCount > 0 && ddof < validCount then
                !IsNaN(result) &&
                var mean := Mean(validValues);
                var sumSqDev := SumSquaredDeviations(validValues, mean);
                var variance := sumSqDev / (validCount - ddof) as real;
                result == RealVal(variance) &&
                variance >= 0.0
            else
                IsNaN(result)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
