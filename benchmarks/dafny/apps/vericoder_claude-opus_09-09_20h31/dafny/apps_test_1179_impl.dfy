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
  // This follows from the fact that TotalIdentifiersAfterRobot is monotonically increasing
}

lemma ExistsRobotContainingK(n: int, k: int)
  requires n >= 1 && k >= 1 && k <= n * (n + 1) / 2
  ensures exists i :: 1 <= i <= n && TotalIdentifiersAfterRobot(i - 1) < k <= TotalIdentifiersAfterRobot(i)
{
  var i := 1;
  while i <= n
    invariant 1 <= i <= n + 1
    invariant forall j :: 1 <= j < i ==> k > TotalIdentifiersAfterRobot(j)
  {
    if TotalIdentifiersAfterRobot(i - 1) < k <= TotalIdentifiersAfterRobot(i) {
      return;
    }
    i := i + 1;
  }
  // At this point i == n + 1, and we know k > TotalIdentifiersAfterRobot(n-1)
  // Since k <= n * (n + 1) / 2 = TotalIdentifiersAfterRobot(n), we have our witness
  assert TotalIdentifiersAfterRobot(n) == n * (n + 1) / 2;
  assert k <= TotalIdentifiersAfterRobot(n);
  assert forall j :: 1 <= j < n ==> k > TotalIdentifiersAfterRobot(j);
  assert TotalIdentifiersAfterRobot(n - 1) < k <= TotalIdentifiersAfterRobot(n);
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, L: seq<int>) returns (result: int)
  requires ValidInput(n, k, L)
  ensures CorrectResult(n, k, L, result)
// </vc-spec>
// <vc-code>
{
  ExistsRobotContainingK(n, k);
  
  var i := 1;
  
  while i <= n
    invariant 1 <= i <= n + 1
    invariant forall j :: 1 <= j < i ==> k > TotalIdentifiersAfterRobot(j)
    invariant exists robot :: i <= robot <= n && TotalIdentifiersAfterRobot(robot - 1) < k <= TotalIdentifiersAfterRobot(robot)
  {
    var totalBefore := (i - 1) * i / 2;
    var totalAfter := i * (i + 1) / 2;
    
    assert TotalIdentifiersAfterRobot(i - 1) == totalBefore;
    assert TotalIdentifiersAfterRobot(i) == totalAfter;
    
    if totalBefore < k && k <= totalAfter {
      var indexInL := k - totalBefore - 1;
      result := L[indexInL];
      
      assert TotalIdentifiersAfterRobot(i - 1) < k <= TotalIdentifiersAfterRobot(i);
      assert result == L[k - TotalIdentifiersAfterRobot(i - 1) - 1];
      assert CorrectResult(n, k, L, result);
      
      return;
    }
    
    assert k > TotalIdentifiersAfterRobot(i);
    i := i + 1;
  }
  
  // This point should be unreachable
  assert false;
}
// </vc-code>

