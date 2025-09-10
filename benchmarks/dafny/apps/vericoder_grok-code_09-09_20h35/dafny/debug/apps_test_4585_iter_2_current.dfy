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
    invariant TriangularNumber(t - 1) < x
    decreases x - TriangularNumber(t)
  {
    t := t + 1;
  }
  return t;
}
// </vc-code>

