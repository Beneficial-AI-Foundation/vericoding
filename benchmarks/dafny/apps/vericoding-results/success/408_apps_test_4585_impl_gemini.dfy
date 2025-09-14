predicate ValidInput(x: int)
{
  x >= 1
}

function TriangularNumber(n: int): int
  requires n >= 0
{
  n * (n + 1) / 2
}

predicate IsMinimalTime(t: int, x: int)
  requires x >= 1
{
  t >= 1 && 
  TriangularNumber(t) >= x &&
  (t == 1 || TriangularNumber(t - 1) < x)
}

// <vc-helpers>
lemma TriangularNumber_Inc(n: int)
  requires n >= 0
  ensures TriangularNumber(n) < TriangularNumber(n + 1)
{
  assert n + 1 > 0;
  assert TriangularNumber(n + 1) - TriangularNumber(n) == n + 1;
}
// </vc-helpers>

// <vc-spec>
method solve(x: int) returns (result: int)
  requires ValidInput(x)
  ensures IsMinimalTime(result, x)
// </vc-spec>
// <vc-code>
{
  var t := 1;
  while TriangularNumber(t) < x
    invariant t >= 1
    invariant t == 1 || TriangularNumber(t - 1) < x
    decreases x - TriangularNumber(t)
  {
    TriangularNumber_Inc(t);
    t := t + 1;
  }
  return t;
}
// </vc-code>

