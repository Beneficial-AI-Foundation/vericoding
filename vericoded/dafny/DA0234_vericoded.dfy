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

// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures result == MinJumps(n)
// </vc-spec>
// <vc-code>
{
    result := (n - 2) * (n - 2);
}
// </vc-code>

