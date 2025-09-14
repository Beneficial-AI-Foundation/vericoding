predicate ValidInput(n: int)
{
    1 <= n <= 10000
}

predicate ValidChange(change: int)
{
    0 <= change <= 999
}

function CorrectChange(n: int): int
    requires ValidInput(n)
{
    (1000 - n % 1000) % 1000
}

// <vc-helpers>
// No helpers needed
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (change: int)
    requires ValidInput(n)
    ensures ValidChange(change)
    ensures change == CorrectChange(n)
// </vc-spec>
// <vc-code>
{
  change := CorrectChange(n);
}
// </vc-code>

