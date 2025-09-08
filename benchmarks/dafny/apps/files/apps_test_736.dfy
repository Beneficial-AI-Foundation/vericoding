Given a staircase with n steps, find the minimum number of moves to reach the top
where each move climbs 1 or 2 steps, and total moves must be a multiple of m.

predicate ValidInput(n: int, m: int)
{
  n > 0 && n <= 10000 && m > 1 && m <= 10
}

function MinMoves(n: int): int
  requires n > 0
{
  if n % 2 == 0 then n / 2 else n / 2 + 1
}

predicate ValidMoveCount(n: int, k: int)
  requires n > 0
{
  MinMoves(n) <= k <= n
}

predicate IsValidSolution(n: int, m: int, result: int)
  requires ValidInput(n, m)
{
  result == -1 || (result > 0 && result % m == 0 && ValidMoveCount(n, result))
}

predicate NoSmallerSolution(n: int, m: int, result: int)
  requires ValidInput(n, m)
{
  result == -1 ==> forall k :: (MinMoves(n) <= k <= n) ==> k % m != 0
}

predicate IsMinimalSolution(n: int, m: int, result: int)
  requires ValidInput(n, m)
{
  result != -1 ==> forall k :: (MinMoves(n) <= k <= n && k < result) ==> k % m != 0
}

method solve(n: int, m: int) returns (result: int)
  requires ValidInput(n, m)
  ensures IsValidSolution(n, m, result)
  ensures NoSmallerSolution(n, m, result)
  ensures IsMinimalSolution(n, m, result)
{
  var p := MinMoves(n);
  
  var w := p;
  while w % m != 0 && w <= n
    invariant p <= w <= n + 1
    invariant forall k :: p <= k < w ==> k % m != 0
    decreases n - w + 1
  {
    w := w + 1;
  }

  if w <= n {
    result := w;
  } else {
    result := -1;
  }
}
