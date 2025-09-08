Given uncovered heights of two adjacent towers after snowfall, find the snow depth.
Towers have triangular number heights: 1, 3, 6, 10, ... (i-th tower height = i*(i+1)/2).
Snow covers uniformly to same depth everywhere.

predicate ValidInput(a: int, b: int)
{
  a >= 1 && b > a && b < 499500
}

predicate ValidSnowDepth(a: int, b: int, depth: int)
{
  depth >= 1 &&
  ((b - a) * (b - a) - (a + b)) >= 2 &&
  ((b - a) * (b - a) - (a + b)) % 2 == 0
}

function SnowDepthFormula(a: int, b: int): int
  requires ValidInput(a, b)
  requires ValidSnowDepth(a, b, ((b - a) * (b - a) - (a + b)) / 2)
{
  ((b - a) * (b - a) - (a + b)) / 2
}

method solve(a: int, b: int) returns (result: int)
  requires ValidInput(a, b)
  requires ValidSnowDepth(a, b, ((b - a) * (b - a) - (a + b)) / 2)
  ensures result >= 1
  ensures result == SnowDepthFormula(a, b)
{
  var diff := b - a;
  var sum := a + b;
  result := (diff * diff - sum) / 2;
}
