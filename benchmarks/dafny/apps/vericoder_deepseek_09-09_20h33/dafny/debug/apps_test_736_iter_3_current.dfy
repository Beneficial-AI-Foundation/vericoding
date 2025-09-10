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
    var i: int := 1;
    if k + add <= n {
      assert k + add <= n;
      assert (k + add) % m == 0;
    } else {
      var steps_back := (rem + m - 1) / m;
      var candidate := k - steps_back * m;
      if candidate >= MinMoves(n) {
        assert candidate <= n;
        assert candidate % m == 0;
      }
    }
  }
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
  
  if min_moves % m == 0 {
    result := min_moves;
  } else {
    var candidate := min_moves + (m - (min_moves % m));
    if candidate <= n {
      result := candidate;
    } else {
      var rem := min_moves % m;
      var steps_back := (rem + m - 1) / m;
      var prev_candidate := min_moves - steps_back * m;
      
      if prev_candidate >= min_moves && prev_candidate % m == 0 {
        result := prev_candidate;
      } else if prev_candidate + m >= min_moves && prev_candidate + m <= n {
        result := prev_candidate + m;
      } else {
        result := -1;
      }
    }
  }
}
// </vc-code>

