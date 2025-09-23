// <vc-preamble>
predicate ValidInput(n: int, k: int)
{
  2 <= n <= 5000 && 1 <= k <= n
}

function OptimalMoves(n: int, k: int): int
  requires ValidInput(n, k)
{
  if k == 1 || k == n then
    3 * n
  else
    3 * n + min(k - 1, n - k)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method MinimumMoves(n: int, k: int) returns (result: int)
  requires ValidInput(n, k)
  ensures result == OptimalMoves(n, k)
  ensures result > 0
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
