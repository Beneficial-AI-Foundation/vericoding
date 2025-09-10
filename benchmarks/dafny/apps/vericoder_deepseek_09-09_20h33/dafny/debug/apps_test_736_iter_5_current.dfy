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
lemma LemmaDivMod(a: int, d: int)
  requires d > 0
  ensures 0 <= a % d < d
{
}

lemma LemmaMinMovesInRange(n: int)
  requires n > 0
  ensures 0 < MinMoves(n) <= n
{
  if n % 2 == 0 {
    assert n / 2 > 0;
    assert n / 2 <= n;
  } else {
    assert n / 2 + 1 > 0;
    assert n / 2 + 1 <= n;
  }
}

lemma LemmaModCycle(n: int, m: int, k: int)
  requires m > 1 && n > 0 && MinMoves(n) <= k <= n
  ensures exists i :: i >= 0 && k + i * m <= n && (k + i * m) % m == 0
{
  var rem := k % m;
  if rem == 0 {
    var i: int := 0;
    assert k + i * m == k <= n;
    assert (k + i * m) % m == 0;
  } else {
    var add := m - rem;
    if k + add <= n {
      var i: int := 1;
      assert k + i * add <= n;
      assert (k + add) % m == 0;
    } else {
      var steps_back := (rem + m - 1) / m;
      var candidate := k - steps_back * m;
      if candidate >= MinMoves(n) {
        assert candidate <= n;
        assert candidate % m == 0;
      } else {
        var additional := MinMoves(n) - candidate;
        var cycles := (additional + m - 1) / m;
        candidate := candidate + cycles * m;
        if candidate <= n {
          assert candidate % m == 0;
        } else {
          candidate := -1;
        }
      }
    }
  }
}

lemma LemmaFindSolutionExists(n: int, m: int)
  requires ValidInput(n, m)
  ensures exists k :: MinMoves(n) <= k <= n && k % m == 0 || 
          (forall k :: MinMoves(n) <= k <= n ==> k % m != 0)
{
}

lemma LemmaNoSolutionCase(n: int, m: int)
  requires ValidInput(n, m)
  requires forall k :: MinMoves(n) <= k <= n ==> k % m != 0
  ensures IsValidSolution(n, m, -1)
  ensures NoSmallerSolution(n, m, -1)
  ensures IsMinimalSolution(n, m, -1)
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
  var min_moves := MinMoves(n);
  var found := false;
  result := -1;
  
  var k := min_moves;
  while k <= n && !found
    invariant min_moves <= k <= n + 1
    invariant !found ==> forall i :: min_moves <= i < k ==> i % m != 0
    invariant found ==> result % m == 0 && min_moves <= result <= n
  {
    if k % m == 0 {
      result := k;
      found := true;
    }
    k := k + 1;
  }
}
// </vc-code>

