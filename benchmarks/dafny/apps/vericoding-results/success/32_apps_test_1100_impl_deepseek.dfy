predicate ValidInput(n: int)
{
    n >= 3
}

function MinJumps(n: int): int
    requires ValidInput(n)
{
    (n - 2) * (n - 2)
}

// <vc-helpers>
lemma SquareLemma(n: int)
  requires n >= 0
  ensures (n + 1) * (n + 1) == n * n + 2 * n + 1
{
}

lemma MinJumpsExpanded(n: int)
  requires ValidInput(n)
  ensures MinJumps(n) == n * n - 4 * n + 4
{
  calc {
    MinJumps(n);
    (n - 2) * (n - 2);
    n * n - 4 * n + 4;
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures result == MinJumps(n)
// </vc-spec>
// <vc-code>
{
  var k := 0;
  var i := 0;
  while i < n - 2
    invariant 0 <= i <= n - 2
    invariant k == i * (n - 2)
  {
    k := k + (n - 2);
    i := i + 1;
  }
  result := k;
}
// </vc-code>

