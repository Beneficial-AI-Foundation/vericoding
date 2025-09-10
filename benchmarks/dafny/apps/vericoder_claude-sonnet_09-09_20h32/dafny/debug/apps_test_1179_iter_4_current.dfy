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
lemma TotalIdentifiersMonotonic(i: int, j: int)
  requires 0 <= i <= j
  ensures TotalIdentifiersAfterRobot(i) <= TotalIdentifiersAfterRobot(j)
{
}

lemma TotalIdentifiersStrictlyIncreasing(i: int)
  requires i >= 0
  ensures TotalIdentifiersAfterRobot(i) < TotalIdentifiersAfterRobot(i + 1)
{
}

lemma FindRobotExists(n: int, k: int)
  requires n >= 1 && k >= 1 && k <= n * (n + 1) / 2
  ensures exists i :: (1 <= i <= n && TotalIdentifiersAfterRobot(i - 1) < k <= TotalIdentifiersAfterRobot(i))
{
  assert TotalIdentifiersAfterRobot(0) == 0;
  assert TotalIdentifiersAfterRobot(n) == n * (n + 1) / 2;
  assert k >= 1 > 0 == TotalIdentifiersAfterRobot(0);
  assert k <= n * (n + 1) / 2 == TotalIdentifiersAfterRobot(n);
}

lemma RobotBoundsLemma(n: int, k: int, i: int)
  requires ValidInput(n, k, seq(n, x => 0))
  requires 1 <= i <= n
  requires TotalIdentifiersAfterRobot(i - 1) < k <= TotalIdentifiersAfterRobot(i)
  ensures 1 <= k - TotalIdentifiersAfterRobot(i - 1) <= i
  ensures 0 <= k - TotalIdentifiersAfterRobot(i - 1) - 1 < i
  ensures k - TotalIdentifiersAfterRobot(i - 1) - 1 < n
{
  var pos := k - TotalIdentifiersAfterRobot(i - 1);
  assert pos >= 1;
  assert pos <= i;
  assert i <= n;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, L: seq<int>) returns (result: int)
  requires ValidInput(n, k, L)
  ensures CorrectResult(n, k, L, result)
// </vc-spec>
// <vc-code>
{
  var i := 1;
  while i <= n
    invariant 1 <= i <= n + 1
    invariant forall j :: 1 <= j < i ==> !(TotalIdentifiersAfterRobot(j - 1) < k <= TotalIdentifiersAfterRobot(j))
  {
    var prevTotal := TotalIdentifiersAfterRobot(i - 1);
    var currTotal := TotalIdentifiersAfterRobot(i);
    
    if prevTotal < k && k <= currTotal {
      RobotBoundsLemma(n, k, i);
      var pos := k - prevTotal - 1;
      result := L[pos];
      return;
    }
    i := i + 1;
  }
  FindRobotExists(n, k);
  assert false;
}
// </vc-code>

