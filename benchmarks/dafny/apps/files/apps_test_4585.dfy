Find the minimum time needed for a kangaroo to reach position X on a number line.
The kangaroo starts at position 0 at time 0. At each time step i (i = 1, 2, 3, ...),
the kangaroo can stay at current position or jump exactly i units left or right.

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

method solve(x: int) returns (result: int)
  requires ValidInput(x)
  ensures IsMinimalTime(result, x)
{
  var ans := 0;
  var a := 0;
  var i := 1;

  while a < x
    invariant ans >= 0
    invariant i == ans + 1
    invariant a == TriangularNumber(ans)
    invariant ans == 0 ==> a == 0
    invariant ans > 0 ==> a > 0
    invariant ans > 0 ==> TriangularNumber(ans - 1) < x
  {
    a := a + i;
    ans := ans + 1;
    i := i + 1;
  }

  if ans == 0 {
    result := 1;
  } else {
    result := ans;
  }
}
