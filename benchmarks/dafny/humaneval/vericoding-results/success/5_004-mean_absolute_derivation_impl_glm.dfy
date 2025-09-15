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
function absoluteDifferences(s: seq<real>, m: real): seq<real>
{
  seq(|s|, i requires 0 <= i < |s| => abs(s[i] - m))
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
  var absDiffSeq := absoluteDifferences(numbers, m);
  derivation := mean(absDiffSeq);
}
// </vc-code>
