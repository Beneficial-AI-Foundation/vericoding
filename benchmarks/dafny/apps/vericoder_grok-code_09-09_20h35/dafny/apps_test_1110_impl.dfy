predicate ValidInput(n: int) {
    n >= 1
}

function WorstCasePresses(n: int): int
    requires ValidInput(n)
{
    n * (n * n + 5) / 6
}

// <vc-helpers>
// No updates needed
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures result == WorstCasePresses(n)
    ensures result >= 1
// </vc-spec>
// <vc-code>
{
  result := n * (n * n + 5) / 6;
}
// </vc-code>

