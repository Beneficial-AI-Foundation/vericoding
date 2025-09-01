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
function mean(s: seq<real>) : real
  requires |s| > 0
{
  sum(s) / |s| as real
}

function abs_diff_seq(s: seq<real>, m: real) : seq<real>
  requires |s| > 0
  ensures |abs_diff_seq(s, m)| == |s|
  ensures forall i :: 0 <= i < |s| ==> abs_diff_seq(s, m)[i] == abs(s[i] - m)
{
  if |s| == 0 then []
  else [abs(s[0] - m)] + abs_diff_seq(s[1..], m)
}
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
  var abs_diffs := abs_diff_seq(numbers, m);
  return mean(abs_diffs);
}
// </vc-code>

