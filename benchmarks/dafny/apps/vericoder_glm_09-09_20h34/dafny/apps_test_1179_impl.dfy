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
lemma TriangularEquation(i: int)
  requires i >= 1
  ensures TotalIdentifiersAfterRobot(i) == TotalIdentifiersAfterRobot(i-1) + i
{
  calc {
    TotalIdentifiersAfterRobot(i);
    i * (i + 1) / 2;
    { assert i >= 1; }
    (i - 1) * i / 2 + i;
    TotalIdentifiersAfterRobot(i - 1) + i;
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
  var low := 0;
  var high := 1;

  while k > high
    invariant 1 <= i <= n
    invariant low == TotalIdentifiersAfterRobot(i-1)
    invariant high == TotalIdentifiersAfterRobot(i)
    invariant low < k
  {
    i := i + 1;
    TriangularEquation(i);
    low := high;
    high := high + i;
  }

  result := L[k - low - 1];
}
// </vc-code>

