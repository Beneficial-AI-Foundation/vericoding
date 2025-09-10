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

// <vc-helpers>
function min(a: int, b: int): int
{
  if a <= b then a else b
}

lemma OptimalMovesPositive(n: int, k: int)
  requires ValidInput(n, k)
  ensures OptimalMoves(n, k) > 0
{
  // Since n >= 2 and k >= 1, we have 3*n >= 6 > 0
  // In all cases, OptimalMoves returns at least 3*n
}
// </vc-helpers>

// <vc-spec>
method MinimumMoves(n: int, k: int) returns (result: int)
  requires ValidInput(n, k)
  ensures result == OptimalMoves(n, k)
  ensures result > 0
// </vc-spec>
// <vc-code>
{
  if k == 1 || k == n {
    result := 3 * n;
  } else {
    var minDist := if k - 1 <= n - k then k - 1 else n - k;
    result := 3 * n + minDist;
  }
  
  // Verify the result is positive
  OptimalMovesPositive(n, k);
}
// </vc-code>

