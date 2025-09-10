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
    var t := if k - 1 <= n - k then k - 1 else n - k;
    result := 3 * n + t;
  }
  assert result > 0;
  assert result == OptimalMoves(n, k);
}
// </vc-code>

