// <vc-preamble>
// ======= TASK =======
// Given a list of floating-point numbers, calculate the Mean Absolute Deviation (MAD) around the arithmetic mean.
// The Mean Absolute Deviation is defined as: MAD = (1/n) × Σ|x_i - mean|
// Where n is the number of elements, x_i is each element, and mean is the arithmetic mean of all elements.

// ======= SPEC REQUIREMENTS =======
function sum(numbers: seq<real>): real
{
    if |numbers| == 0 then 0.0
    else numbers[0] + sum(numbers[1..])
}

function abs(x: real): real
{
    if x >= 0.0 then x else -x
}

predicate ValidInput(numbers: seq<real>)
{
    |numbers| > 0
}

function ArithmeticMean(numbers: seq<real>): real
    requires ValidInput(numbers)
{
    sum(numbers) / (|numbers| as real)
}

function AbsoluteDeviations(numbers: seq<real>): seq<real>
    requires ValidInput(numbers)
{
    seq(|numbers|, i requires 0 <= i < |numbers| => abs(numbers[i] - ArithmeticMean(numbers)))
}

function MAD(numbers: seq<real>): real
    requires ValidInput(numbers)
{
    sum(AbsoluteDeviations(numbers)) / (|numbers| as real)
}
// </vc-preamble>

// <vc-helpers>
// ======= HELPERS =======
lemma sum_non_negative(numbers: seq<real>)
    requires forall i :: 0 <= i < |numbers| ==> numbers[i] >= 0.0
    ensures sum(numbers) >= 0.0
{
    if |numbers| == 0 {
        // Base case: empty sequence has sum 0.0
    } else {
        // Inductive case: numbers[0] >= 0.0 and sum(numbers[1..]) >= 0.0
        sum_non_negative(numbers[1..]);
    }
}
// </vc-helpers>

// <vc-spec>
// ======= MAIN METHOD =======
method mean_absolute_deviation(numbers: seq<real>) returns (result: real)
    requires ValidInput(numbers)
    ensures result >= 0.0
    ensures result == MAD(numbers)
// </vc-spec>
// <vc-code>
{
    // Calculate the mean of the numbers
    var mean := sum(numbers) / (|numbers| as real);

    // Calculate the absolute deviations from the mean
    var absolute_deviations: seq<real> := [];
    for i := 0 to |numbers|
        invariant 0 <= i <= |numbers|
        invariant |absolute_deviations| == i
        invariant forall j :: 0 <= j < i ==> absolute_deviations[j] == abs(numbers[j] - mean)
        invariant forall j :: 0 <= j < i ==> absolute_deviations[j] >= 0.0
    {
        var tmpCall1 := abs(numbers[i] - mean);
        absolute_deviations := absolute_deviations + [tmpCall1];
    }

    // Return the mean of the absolute deviations
    assert |absolute_deviations| == |numbers| > 0;
    assert forall j :: 0 <= j < |absolute_deviations| ==> absolute_deviations[j] >= 0.0;
    sum_non_negative(absolute_deviations);
    assert sum(absolute_deviations) >= 0.0;
    result := sum(absolute_deviations) / (|absolute_deviations| as real);

    // Prove the postcondition
    assert absolute_deviations == seq(|numbers|, i requires 0 <= i < |numbers| => abs(numbers[i] - mean));
    assert result == sum(seq(|numbers|, i requires 0 <= i < |numbers| => abs(numbers[i] - mean))) / (|numbers| as real);
}
// </vc-code>
