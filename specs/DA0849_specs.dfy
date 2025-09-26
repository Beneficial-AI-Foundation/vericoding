// <vc-preamble>
predicate ValidInput(x: int, t: int)
{
    1 <= x <= 1000000000 && 1 <= t <= 1000000000
}

function SandRemaining(x: int, t: int): int
{
    if x >= t then x - t else 0
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(x: int, t: int) returns (result: int)
    requires ValidInput(x, t)
    ensures result >= 0
    ensures result == SandRemaining(x, t)
    ensures result <= x
// </vc-spec>
// <vc-code>
{
    if x >= t {
        result := x - t;
    } else {
        result := 0;
    }
}
// </vc-code>
