// <vc-preamble>

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
lemma sum_non_negative(numbers: seq<real>)
    requires forall i :: 0 <= i < |numbers| ==> numbers[i] >= 0.0
    ensures sum(numbers) >= 0.0
{
    if |numbers| == 0 {
    } else {
        sum_non_negative(numbers[1..]);
    }
}
// </vc-preamble>

// <vc-helpers>
lemma absolute_deviations_non_negative(numbers: seq<real>)
    requires ValidInput(numbers)
    ensures forall i :: 0 <= i < |AbsoluteDeviations(numbers)| ==> AbsoluteDeviations(numbers)[i] >= 0.0
{
}

lemma mad_non_negative(numbers: seq<real>)
    requires ValidInput(numbers)
    ensures MAD(numbers) >= 0.0
{
    absolute_deviations_non_negative(numbers);
    sum_non_negative(AbsoluteDeviations(numbers));
}
// </vc-helpers>

// <vc-spec>
method mean_absolute_deviation(numbers: seq<real>) returns (result: real)
    requires ValidInput(numbers)
    ensures result >= 0.0
    ensures result == MAD(numbers)
// </vc-spec>
// <vc-code>
{
    result := MAD(numbers);
    mad_non_negative(numbers);
}
// </vc-code>
