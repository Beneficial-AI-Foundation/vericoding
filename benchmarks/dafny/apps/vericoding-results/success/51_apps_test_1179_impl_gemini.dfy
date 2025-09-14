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
lemma TotalIdRecursive(i: int)
  requires i >= 1
  ensures TotalIdentifiersAfterRobot(i) == TotalIdentifiersAfterRobot(i - 1) + i
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
  var i := 1;
  var total_so_far := 0;

  while i <= n
    invariant 1 <= i <= n + 1
    invariant total_so_far == TotalIdentifiersAfterRobot(i - 1)
    invariant k > total_so_far
  {
    TotalIdRecursive(i);
    var next_total := total_so_far + i;
    if k <= next_total {
      var index := k - total_so_far - 1;
      result := L[index];
      return;
    }
    total_so_far := next_total;
    i := i + 1;
  }
  assert false;
}
// </vc-code>

