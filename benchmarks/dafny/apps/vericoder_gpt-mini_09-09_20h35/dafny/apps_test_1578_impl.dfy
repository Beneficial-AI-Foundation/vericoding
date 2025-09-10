predicate ValidInput(n: int) {
    n >= 1
}

function MaxSum(n: int): int
    requires n >= 1
{
    n * (n - 1) / 2
}

// <vc-helpers>
// No helper functions or lemmas required for this verification.
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures result == MaxSum(n)
// </vc-spec>
// <vc-code>
{
  result := n * (n - 1) / 2;
}
// </vc-code>

