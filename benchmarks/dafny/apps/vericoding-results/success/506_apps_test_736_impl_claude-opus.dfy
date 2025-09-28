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

lemma NoSolutionCorrectness(n: int, m: int, minMoves: int)
  requires ValidInput(n, m)
  requires minMoves == MinMoves(n)
  requires forall k :: minMoves <= k <= n ==> k % m != 0
  ensures NoSmallerSolution(n, m, -1)
{
  // By definition, if no k in range is divisible by m, then -1 is correct
}

lemma SolutionMinimality(n: int, m: int, k: int, minMoves: int)
  requires ValidInput(n, m)
  requires minMoves == MinMoves(n)
  requires minMoves <= k <= n
  requires k % m == 0
  requires forall j :: minMoves <= j < k ==> j % m != 0
  ensures IsMinimalSolution(n, m, k)
{
  // By construction, k is the minimal solution
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
  var minMoves := MinMoves(n);
  MinMovesProperties(n);
  
  var k := minMoves;
  
  while k <= n
    invariant minMoves <= k <= n + 1
    invariant forall j :: minMoves <= j < k ==> j % m != 0
  {
    if k % m == 0 {
      assert ValidMoveCount(n, k);
      SolutionMinimality(n, m, k, minMoves);
      return k;
    }
    k := k + 1;
  }
  
  NoSolutionCorrectness(n, m, minMoves);
  return -1;
}
// </vc-code>

