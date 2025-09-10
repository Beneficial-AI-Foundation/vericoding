predicate ValidInput(N: int, D: int)
{
  N >= 1 && N <= 20 && D >= 1 && D <= 20
}

function CoverageRange(position: int, D: int): (int, int)
{
  (position - D, position + D)
}

predicate TreesCovered(N: int, D: int, inspectors: int)
{
  inspectors >= 1 && inspectors <= N && inspectors == ((N - 1) / (2 * D + 1)) + 1
}

// <vc-helpers>
function method CeilDiv(a: int, b: int): int
  requires b > 0
  ensures CeilDiv(a, b) * b >= a
  ensures (CeilDiv(a, b) - 1) * b < a
{
  (a + b - 1) / b
}
// </vc-helpers>

// <vc-spec>

// </vc-spec>
// <vc-code>
{
  return CeilDiv(N, 2 * D + 1);
}
// </vc-code>

