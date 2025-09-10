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
// No updates needed to helpers; the original empty helpers section is sufficient.
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, L: seq<int>) returns (result: int)
  requires ValidInput(n, k, L)
  ensures CorrectResult(n, k, L, result)
// </vc-spec>
// <vc-code>
{
  var cum := 0;
  var i := 0;
  while cum < k && i < n
    invariant 0 <= i <= n && cum == i * (i + 1) / 2
    decreases n - i
  {
    i := i + 1;
    cum := cum + i;
  }
  // After the loop, i <= n and cum >= k, as per Invariants
  var index := k - cum + i - 1;
  result := L[index];
}
// </vc-code>

