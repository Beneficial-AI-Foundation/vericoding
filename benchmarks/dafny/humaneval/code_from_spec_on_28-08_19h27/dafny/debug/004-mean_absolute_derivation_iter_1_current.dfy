function sum(s: seq<real>) : real {
  if |s| == 0 then 0.0 else s[0] + sum(s[1..])
}
function abs(x: real) : real
  ensures abs(x) >= 0.0
{
  if x >= 0.0 then x else -x
}
function mean(s: seq<real>) : real
  requires |s| > 0
{
  sum(s) / |s| as real
}

// <vc-helpers>
lemma SumNonNegative(s: seq<real>)
  requires forall i :: 0 <= i < |s| ==> s[i] >= 0.0
  ensures sum(s) >= 0.0
{
  if |s| == 0 {
  } else {
    SumNonNegative(s[1..]);
  }
}

lemma AbsDeviationNonNegative(s: seq<real>, m: real)
  ensures forall i :: 0 <= i < |s| ==> abs(s[i] - m) >= 0.0
{
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def mean_absolute_deviation(numbers: List[float]) -> float
For a given list of input numbers, calculate Mean Absolute Deviation around the mean of this dataset. Mean Absolute Deviation is the average absolute difference between each element and a centerpoint (mean in this case): MAD = average | x - x_mean |
*/
// </vc-description>

// <vc-spec>
function mean_absolute_deviation(numbers: seq<real>) : real
  requires |numbers| > 0
  ensures mean_absolute_deviation(numbers) >= 0.0
// </vc-spec>
// <vc-code>
{
  var m := mean(numbers);
  var deviations := seq(|numbers|, i requires 0 <= i < |numbers| => abs(numbers[i] - m));
  SumNonNegative(deviations);
  sum(deviations) / |numbers| as real
}
// </vc-code>
