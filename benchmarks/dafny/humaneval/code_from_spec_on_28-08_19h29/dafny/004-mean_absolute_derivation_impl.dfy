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
function sum_absolute_deviations(s: seq<real>, m: real) : real {
  if |s| == 0 then 0.0 else abs(s[0] - m) + sum_absolute_deviations(s[1..], m)
}

lemma SumAbsoluteDeviationsNonNegative(s: seq<real>, m: real)
  ensures sum_absolute_deviations(s, m) >= 0.0
{
  if |s| == 0 {
    assert sum_absolute_deviations(s, m) == 0.0;
  } else {
    assert abs(s[0] - m) >= 0.0;
    SumAbsoluteDeviationsNonNegative(s[1..], m);
    assert sum_absolute_deviations(s, m) == abs(s[0] - m) + sum_absolute_deviations(s[1..], m);
    assert sum_absolute_deviations(s, m) >= 0.0;
  }
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
  var total_deviation := sum_absolute_deviations(numbers, m);
  SumAbsoluteDeviationsNonNegative(numbers, m);
  assert total_deviation >= 0.0;
  total_deviation / |numbers| as real
}
// </vc-code>
