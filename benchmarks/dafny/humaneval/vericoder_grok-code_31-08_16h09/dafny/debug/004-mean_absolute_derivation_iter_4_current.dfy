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
// Empty - no changes needed
// </vc-helpers>

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
  var sum_diffs := 0.0;
  for i := 0 to |numbers| - 1
    invariant 0 <= i <= |numbers|
    invariant sum_diffs == sum(seq(i, j requires 0 <= j < i => abs(numbers[j] - m)))
  {
    sum_diffs := sum_diffs + abs(numbers[i] - m);
  }
  derivation := sum_diffs / (|numbers| as real);
}
// </vc-code>

