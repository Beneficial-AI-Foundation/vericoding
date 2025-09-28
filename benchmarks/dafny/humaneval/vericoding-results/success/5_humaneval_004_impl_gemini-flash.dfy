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
/* helper modified by LLM (iteration 2): Removed the problematic 'reads s' clause as 's' is a sequence and not an object that can be read from in that context */
function seq_sum_non_negative(s: seq<real>): bool
    ensures seq_sum_non_negative(s) == (forall i :: 0 <= i < |s| ==> s[i] >= 0.0)
{
    forall i :: 0 <= i < |s| ==> s[i] >= 0.0
}
// </vc-helpers>

// <vc-spec>
method mean_absolute_deviation(numbers: seq<real>) returns (result: real)
    requires ValidInput(numbers)
    ensures result >= 0.0
    ensures result == MAD(numbers)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Fixed type conversion errors and used |numbers| for division. */
{
    var mean := ArithmeticMean(numbers);
    var deviations_seq := AbsoluteDeviations(numbers);
    
    // Prove that all elements in deviations_seq are non-negative
    forall i | 0 <= i < |deviations_seq|
        ensures deviations_seq[i] >= 0.0
    {
        // We know abs(x) >= 0.0 for any real x
    }
    
    // Call the helper lemma to ensure sum(deviations_seq) is non-negative
    sum_non_negative(deviations_seq);

    result := sum(deviations_seq) / (|numbers| as real);
}
// </vc-code>
