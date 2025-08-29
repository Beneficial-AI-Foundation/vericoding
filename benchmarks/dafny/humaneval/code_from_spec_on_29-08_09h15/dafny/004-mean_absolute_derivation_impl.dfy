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
lemma SumDistributivity(s1: seq<real>, s2: seq<real>)
  requires |s1| == |s2|
  ensures sum(seq(|s1|, i requires 0 <= i < |s1| => s1[i] + s2[i])) == sum(s1) + sum(s2)
{
  if |s1| == 0 {
  } else {
    var combined := seq(|s1|, i requires 0 <= i < |s1| => s1[i] + s2[i]);
    assert combined[0] == s1[0] + s2[0];
    assert combined[1..] == seq(|s1[1..]|, i requires 0 <= i < |s1[1..]| => s1[1..][i] + s2[1..][i]);
    SumDistributivity(s1[1..], s2[1..]);
    assert sum(combined[1..]) == sum(s1[1..]) + sum(s2[1..]);
    assert sum(combined) == combined[0] + sum(combined[1..]);
    assert sum(combined) == (s1[0] + s2[0]) + (sum(s1[1..]) + sum(s2[1..]));
    assert sum(combined) == (s1[0] + sum(s1[1..])) + (s2[0] + sum(s2[1..]));
    assert sum(combined) == sum(s1) + sum(s2);
  }
}

lemma SeqConstructHelper<T>(s: seq<T>, f: int -> T)
  requires |s| > 0
  requires forall i :: 0 <= i < |s| ==> s[i] == f(i)
  ensures s == seq(|s|, f)
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
method mean_absolute_derivation(numbers: seq<real>) returns (derivation: real)
  // pre-conditions-start
  requires |numbers| > 0
  // pre-conditions-end
  // post-conditions-start
  ensures var m := mean(numbers);
    derivation == mean(seq(|numbers|, i requires 0 <= i < |numbers| => abs(numbers[i] - m)))
  // post-conditions-end
// </vc-spec>

// <vc-code>
{
  var m := mean(numbers);
  var deviations := seq(|numbers|, i requires 0 <= i < |numbers| => abs(numbers[i] - m));
  derivation := mean(deviations);
}
// </vc-code>

