// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No changes needed. */
function ComputeResult(N: int, D: int): int
{
  (N - 1) / (2 * D + 1) + 1
}
// </vc-helpers>

// <vc-spec>
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Simplified the code to a single return statement after removing unnecessary `inspectors` variable declaration. */
{
  return (N - 1) / (2 * D + 1) + 1;
}
// </vc-code>
