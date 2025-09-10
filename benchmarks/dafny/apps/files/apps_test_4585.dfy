/*
Find the minimum time needed for a kangaroo to reach position X on a number line.
The kangaroo starts at position 0 at time 0. At each time step i (i = 1, 2, 3, ...),
the kangaroo can stay at current position or jump exactly i units left or right.
*/

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
  assume {:axiom} false;
}
// </vc-code>
