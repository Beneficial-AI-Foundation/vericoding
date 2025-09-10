predicate ValidInput(n: int, m: int)
{
    2 <= n <= 100 && 2 <= m <= 100
}

function CountBlocks(n: int, m: int): int
    requires ValidInput(n, m)
{
    (n - 1) * (m - 1)
}

predicate CorrectOutput(n: int, m: int, blocks: int)
{
    ValidInput(n, m) && blocks == CountBlocks(n, m)
}

// <vc-helpers>
lemma CountBlocksNonNegative(n: int, m: int)
    requires ValidInput(n, m)
    ensures CountBlocks(n, m) >= 1
{
    // Since 2 <= n <= 100 and 2 <= m <= 100,
    // n - 1 >= 1 and m - 1 >= 1.
    // Therefore, (n - 1) * (m - 1) >= 1 * 1 = 1.
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int) returns (blocks: int)
    requires ValidInput(n, m)
    ensures CorrectOutput(n, m, blocks)
    ensures blocks >= 1
// </vc-spec>
// <vc-code>
{
    blocks := (n - 1) * (m - 1);
    CountBlocksNonNegative(n, m); // To prove blocks >= 1
}
// </vc-code>

