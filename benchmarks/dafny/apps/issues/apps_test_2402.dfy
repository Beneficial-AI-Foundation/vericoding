// <vc-preamble>
predicate ValidInput(n: nat, x: nat, y: nat)
{
  1 <= n <= 1000000000 && 1 <= x <= n && 1 <= y <= n
}

function NikolayScore(x: nat, y: nat): nat
{
  x + y
}

function ComputeMinPlace(n: nat, x: nat, y: nat): nat
  requires ValidInput(n, x, y)
{
  var s := NikolayScore(x, y);
  if s <= n then 1 else min3(s, s - n + 1, n)
}

function ComputeMaxPlace(n: nat, x: nat, y: nat): nat
  requires ValidInput(n, x, y)
{
  var s := NikolayScore(x, y);
  if s - 1 < n then s - 1 else n
}

function min3(a: nat, b: nat, c: nat): nat
{
  if a <= b && a <= c then a
  else if b <= c then b
  else c
}

predicate ValidOutput(n: nat, x: nat, y: nat, minPlace: nat, maxPlace: nat)
  requires ValidInput(n, x, y)
{
  minPlace == ComputeMinPlace(n, x, y) &&
  maxPlace == ComputeMaxPlace(n, x, y) &&
  1 <= minPlace <= maxPlace <= n
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method FindMinMaxPlace(n: nat, x: nat, y: nat) returns (minPlace: nat, maxPlace: nat)
  requires ValidInput(n, x, y)
  ensures ValidOutput(n, x, y, minPlace, maxPlace)
  ensures minPlace == ComputeMinPlace(n, x, y)
  ensures maxPlace == ComputeMaxPlace(n, x, y)
  ensures 1 <= minPlace <= maxPlace <= n
// </vc-spec>
// <vc-code>
{
  var s := x + y;
  maxPlace := if s - 1 < n then s - 1 else n;
  minPlace := if s <= n then 1 else min3(s, s - n + 1, n);
}
// </vc-code>
