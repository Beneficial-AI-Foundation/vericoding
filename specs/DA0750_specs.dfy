// <vc-preamble>
predicate ValidInput(w1: int, h1: int, w2: int, h2: int)
{
    1 <= w1 <= 1000000000 &&
    1 <= h1 <= 1000000000 &&
    1 <= w2 <= 1000000000 &&
    1 <= h2 <= 1000000000 &&
    w1 >= w2
}

function AdjacentCellCount(w1: int, h1: int, w2: int, h2: int): int
    requires ValidInput(w1, h1, w2, h2)
{
    2 * (h1 + h2) + w1 + w2 + (w1 - w2) + 4
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(w1: int, h1: int, w2: int, h2: int) returns (result: int)
    requires ValidInput(w1, h1, w2, h2)
    ensures result == AdjacentCellCount(w1, h1, w2, h2)
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
    result := 2 * (h1 + h2) + w1 + w2 + (w1 - w2) + 4;
}
// </vc-code>
