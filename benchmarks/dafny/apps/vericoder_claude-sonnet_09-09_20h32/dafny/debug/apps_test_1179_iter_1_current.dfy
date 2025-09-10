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
  ensures exists i :: 1 <= i <= n && 
    TotalIdentifiersAfterRobot(i - 1) < k <= TotalIdentifiersAfterRobot(i)
{
  assert TotalIdentifiersAfterRobot(0) == 0;
  assert TotalIdentifiersAfterRobot(n) == n * (n + 1) / 2;
  assert k >= 1 > 0 == TotalIdentifiersAfterRobot(0);
  assert k <= n * (n + 1) / 2 == TotalIdentifiersAfterRobot(n);
}

lemma FindRobotUnique(n: int, k: int)
  requires n >= 1 && k >= 1 && k <= n * (n + 1) / 2
  ensures exists! i :: 1 <= i <= n && 
    TotalIdentifiersAfterRobot(i - 1) < k <= TotalIdentifiersAfterRobot(i)
{
  FindRobotExists(n, k);
  forall i, j | 1 <= i <= n && 1 <= j <= n && i != j &&
    TotalIdentifiersAfterRobot(i - 1) < k <= TotalIdentifiersAfterRobot(i) &&
    TotalIdentifiersAfterRobot(j - 1) < k <= TotalIdentifiersAfterRobot(j)
    ensures false
  {
    if i < j {
      TotalIdentifiersStrictlyIncreasing(i - 1);
      assert TotalIdentifiersAfterRobot(i) <= TotalIdentifiersAfterRobot(i - 1) + i;
      assert k <= TotalIdentifiersAfterRobot(i) < TotalIdentifiersAfterRobot(j - 1) < k;
    } else {
      TotalIdentifiersStrictlyIncreasing(j - 1);
      assert k <= TotalIdentifiersAfterRobot(j) < TotalIdentifiersAfterRobot(i - 1) < k;
    }
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
  var i := 1;
  while i <= n
    invariant 1 <= i <= n + 1
    invariant forall j :: 1 <= j < i ==> !(TotalIdentifiersAfterRobot(j - 1) < k <= TotalIdentifiersAfterRobot(j))
  {
    if TotalIdentifiersAfterRobot(i - 1) < k <= TotalIdentifiersAfterRobot(i) {
      FindRobotUnique(n, k);
      var pos := k - TotalIdentifiersAfterRobot(i - 1) - 1;
      assert 0 <= pos < i;
      assert pos < |L|;
      result := L[pos];
      return;
    }
    i := i + 1;
  }
  FindRobotExists(n, k);
  assert false;
}
// </vc-code>

