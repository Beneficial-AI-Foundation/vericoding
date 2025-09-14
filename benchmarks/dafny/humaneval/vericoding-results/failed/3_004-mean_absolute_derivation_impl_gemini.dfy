// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
lemma SumAppend(s1: seq<real>, s2: seq<real>)
  ensures sum(s1 + s2) == sum(s1) + sum(s2)
{
  if |s1| > 0 {
    calc {
      sum(s1 + s2);
      sum([s1[0]] + (s1[1..] + s2));
      s1[0] + sum(s1[1..] + s2);
      { SumAppend(s1[1..], s2); }
      s1[0] + sum(s1[1..]) + sum(s2);
      (s1[0] + sum(s1[1..])) + sum(s2);
      sum(s1) + sum(s2);
    }
  }
}
// </vc-helpers>

// <vc-spec>
method mean_absolute_derivation(numbers: seq<real>) returns (derivation: real)

  requires |numbers| > 0

  ensures var m := mean(numbers);
    derivation == mean(seq(|numbers|, i requires 0 <= i < |numbers| => abs(numbers[i] - m)))
// </vc-spec>
// <vc-code>
{
  var m := mean(numbers);
  var n := |numbers|;

  ghost var deviations_s := seq(n, i => abs(numbers[i] - m));

  var sum_of_deviations: real := 0.0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant sum_of_deviations == sum(deviations_s[..i])
  {
    SumAppend(deviations_s[..i], [deviations_s[i]]);
    sum_of_deviations := sum_of_deviations + abs(numbers[i] - m);
    i := i + 1;
  }

  derivation := sum_of_deviations / (n as real);
}
// </vc-code>
