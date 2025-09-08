Given n manholes in a line (positions 1 to n), each initially covered by one stone with one coin underneath.
Nastya starts at position k and can: throw stones, move to adjacent positions, or collect coins from uncovered manholes.
Find the minimum number of moves needed to collect all n coins.

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

function min(a: int, b: int): int
{
  if a <= b then a else b
}

function solve(n: int, k: int): int
  requires ValidInput(n, k)
  ensures solve(n, k) > 0
  ensures (k == 1 || k == n) ==> solve(n, k) == 3 * n
  ensures (k != 1 && k != n) ==> solve(n, k) == 3 * n + min(k - 1, n - k)
  ensures solve(n, k) == OptimalMoves(n, k)
{
  if k == 1 || k == n then
    3 * n
  else
    3 * n + min(k - 1, n - k)
}

method MinimumMoves(n: int, k: int) returns (result: int)
  requires ValidInput(n, k)
  ensures result == OptimalMoves(n, k)
  ensures result > 0
{
  result := solve(n, k);
}
