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
lemma TotalIdentifiersIncreases(i: int, j: int)
  requires 0 <= i <= j
  ensures TotalIdentifiersAfterRobot(i) <= TotalIdentifiersAfterRobot(j)
{
}

lemma TotalIdentifiersStrictlyIncreases(i: int, j: int)
  requires 0 <= i < j
  ensures TotalIdentifiersAfterRobot(i) < TotalIdentifiersAfterRobot(j)
{
}

lemma TotalIdentifiersBetween(i: int)
  requires i >= 0
  ensures TotalIdentifiersAfterRobot(i) >= i
{
}

lemma FindIndex(n: int, k: int) returns (i: int)
  requires n >= 1 && k >= 1 && k <= n * (n + 1) / 2
  ensures 1 <= i <= n
  ensures TotalIdentifiersAfterRobot(i - 1) < k <= TotalIdentifiersAfterRobot(i)
{
  i := 1;
  while i <= n && TotalIdentifiersAfterRobot(i) < k
    invariant 1 <= i <= n + 1
    invariant TotalIdentifiersAfterRobot(i - 1) < k
  {
    i := i + 1;
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
  var found := false;
  while i <= n && !found
    invariant 1 <= i <= n + 1
    invariant TotalIdentifiersAfterRobot(i - 1) < k
  {
    if k <= TotalIdentifiersAfterRobot(i) {
      found := true;
    } else {
      i := i + 1;
    }
  }
  
  var offset := k - TotalIdentifiersAfterRobot(i - 1) - 1;
  result := L[offset];
}
// </vc-code>

