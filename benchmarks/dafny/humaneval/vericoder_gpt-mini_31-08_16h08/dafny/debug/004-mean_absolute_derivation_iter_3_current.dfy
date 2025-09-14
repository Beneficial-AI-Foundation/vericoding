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
// (no helpers needed)
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
  var n := |numbers|;
  var m := mean(numbers);
  assert n == |numbers|;
  assert n > 0;
  var a := new real[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> a[j] == abs(numbers[j] - m)
  {
    a[i] := abs(numbers[i] - m);
    i := i + 1;
  }
  var s := a[..];
  assert forall j :: 0 <= j < n ==> s[j] == abs(numbers[j] - m);
  assert s == seq(n, i => abs(numbers[i] - m));
  derivation := mean(s);
  assert derivation == mean(seq(|numbers|, i requires 0 <= i < |numbers| => abs(numbers[i] - m)));
}
// </vc-code>

