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
lemma TriStep(i: int)
  requires i >= 0
  ensures TotalIdentifiersAfterRobot(i + 1) == TotalIdentifiersAfterRobot(i) + i + 1
{
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, L: seq<int>) returns (result: int)
  requires ValidInput(n, k, L)
  ensures CorrectResult(n, k, L, result)
// </vc-spec>
// <vc-code>
{
  var i := n;
  while TotalIdentifiersAfterRobot(i - 1) >= k
    invariant 1 <= i && i <= n
    invariant TotalIdentifiersAfterRobot(i) >= k
    decreases i
  {
    i := i - 1;
  }
  assert TotalIdentifiersAfterRobot(i - 1) < k;
  var j := k - TotalIdentifiersAfterRobot(i - 1) - 1;
  assert j >= 0;

  TriStep(i - 1);
  assert k <= TotalIdentifiersAfterRobot(i - 1) + i;
  assert k - TotalIdentifiersAfterRobot(i - 1) <= i;
  assert j <= i - 1;
  assert j < i;
  assert i <= n;
  assert j < n;

  result := L[j];

  assert 1 <= i && i <= n;
  assert TotalIdentifiersAfterRobot(i - 1) < k <= TotalIdentifiersAfterRobot(i);
  assert result == L[k - TotalIdentifiersAfterRobot(i - 1) - 1];
}
// </vc-code>

