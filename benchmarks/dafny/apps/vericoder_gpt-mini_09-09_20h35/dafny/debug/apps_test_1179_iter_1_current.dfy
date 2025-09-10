predicate ValidInput(n: int, k: int, L: seq<int>)
{
  n >= 1 && k >= 1 && |L| == n && k <= n * (n + 1) / 2
}

function TotalIdentifiersAfterRobot(i: int): int
  requires i >= 0
{
  i * (i + 1) / 2
}

predicate CorrectResult(n: int, k: int, L: seq<int>, result: int)
  requires ValidInput(n, k, L)
{
  exists i :: 1 <= i <= n && 
    TotalIdentifiersAfterRobot(i - 1) < k <= TotalIdentifiersAfterRobot(i) &&
    result == L[k - TotalIdentifiersAfterRobot(i - 1) - 1]
}

// <vc-helpers>
lemma TotalIdentifiersStep(j: int)
  requires j >= 1
  ensures TotalIdentifiersAfterRobot(j) == TotalIdentifiersAfterRobot(j - 1) + j
{
  calc {
    TotalIdentifiersAfterRobot(j);
    = j * (j + 1) / 2;
    = ((j - 1) * j + 2 * j) / 2;
    = (j - 1) * j / 2 + j;
    = TotalIdentifiersAfterRobot(j - 1) + j;
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, L: seq<int>) returns (result: int)
  requires ValidInput(n, k, L)
  ensures CorrectResult(n, k, L, result)
// </vc-spec>
// <vc-code>
{
  var j := 1;
  var t := 0;
  while t + j < k
    invariant 1 <= j <= n
    invariant t == TotalIdentifiersAfterRobot(j - 1)
    invariant t < k
    decreases n - j + 1
  {
    assert j < n by {
      if j == n {
        // from the loop guard
        assert t + j < k;
        // t + j == TotalIdentifiersAfterRobot(j)
        TotalIdentifiersStep(j);
        assert t + j == TotalIdentifiersAfterRobot(j);
        // but by precondition k <= TotalIdentifiersAfterRobot(n), contradiction
        assert k <= TotalIdentifiersAfterRobot(n);
        assert false;
      }
    }
    t := t + j;
    j := j + 1;
  }
  // At this point: t == TotalIdentifiersAfterRobot(j - 1), t < k, and t + j >= k,
  // hence TotalIdentifiersAfterRobot(j - 1) < k <= TotalIdentifiersAfterRobot(j)
  var idx := k - t - 1;
  // prove index is within bounds 0..n-1
  assert 0 <= idx;
  assert k - t <= j;
  assert k - t - 1 <= j - 1;
  assert j - 1 < n;
  assert idx < n;
  result := L[idx];
}
// </vc-code>

