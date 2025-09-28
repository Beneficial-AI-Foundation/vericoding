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
lemma AbsNonNegative(x: real)
    ensures abs(x) >= 0.0
{
    if x >= 0.0 {
        assert abs(x) == x;
        assert x >= 0.0;
    } else {
        assert abs(x) == -x;
        assert -x > 0.0;
    }
    assert abs(x) >= 0.0;
}

lemma AbsoluteDeviations_nonneg(numbers: seq<real>)
    requires ValidInput(numbers)
    ensures forall i :: 0 <= i < |AbsoluteDeviations(numbers)| ==> AbsoluteDeviations(numbers)[i] >= 0.0
{
    var m := ArithmeticMean(numbers);
    var i := 0;
    while i < |numbers|
        invariant 0 <= i <= |numbers|
        invariant forall j :: 0 <= j < i ==> AbsoluteDeviations(numbers)[j] >= 0.0
    {
        assert AbsoluteDeviations(numbers)[i] == abs(numbers[i] - m);
        AbsNonNegative(numbers[i] - m);
        i := i + 1;
    }
}

lemma MAD_nonneg(numbers: seq<real>)
    requires ValidInput(numbers)
    ensures MAD(numbers) >= 0.0
{
    AbsoluteDeviations_nonneg(numbers);
    sum_non_negative(AbsoluteDeviations(numbers));
    var s := sum(AbsoluteDeviations(numbers));
    assert s >= 0.0;
    assert |numbers| > 0;
    assert (|numbers| as real) > 0.0;
    assert s / (|numbers| as real) >= 0.0;
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
  MAD_nonneg(numbers);
  result := MAD(numbers);
}

// </vc-code>
