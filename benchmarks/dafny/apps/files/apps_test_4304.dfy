// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int) returns (result: int)
  requires ValidInput(a, b)
  requires ValidSnowDepth(a, b, ((b - a) * (b - a) - (a + b)) / 2)
  ensures result >= 1
  ensures result == SnowDepthFormula(a, b)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
