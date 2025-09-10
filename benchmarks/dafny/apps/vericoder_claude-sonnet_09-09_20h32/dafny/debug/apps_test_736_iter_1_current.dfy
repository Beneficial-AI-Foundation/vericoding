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

// <vc-helpers>
lemma MinMovesProperties(n: int)
  requires n > 0
  ensures MinMoves(n) > 0
  ensures MinMoves(n) <= n
{
  if n % 2 == 0 {
    assert MinMoves(n) == n / 2;
    assert n / 2 > 0;
    assert n / 2 <= n;
  } else {
    assert MinMoves(n) == n / 2 + 1;
    assert n / 2 + 1 > 0;
    assert n / 2 + 1 <= n;
  }
}

lemma IterationInvariant(n: int, m: int, k: int)
  requires ValidInput(n, m)
  requires MinMoves(n) <= k <= n
  ensures ValidMoveCount(n, k)
{
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int) returns (result: int)
  requires ValidInput(n, m)
  ensures IsValidSolution(n, m, result)
  ensures NoSmallerSolution(n, m, result)
  ensures IsMinimalSolution(n, m, result)
// </vc-spec>
// <vc-code>
{
  MinMovesProperties(n);
  var minMoves := MinMoves(n);
  var k := minMoves;
  
  while k <= n
    invariant minMoves <= k <= n + 1
    invariant forall j :: (minMoves <= j < k) ==> j % m != 0
    decreases n - k
  {
    if k % m == 0 {
      result := k;
      return;
    }
    k := k + 1;
  }
  
  result := -1;
}
// </vc-code>

