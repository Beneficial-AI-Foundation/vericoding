predicate ValidInput(a: int, b: int)
{
    1 <= a <= 12 && 1 <= b <= 31
}

function TakahashiCount(a: int, b: int): int
    requires ValidInput(a, b)
{
    if a > b then a - 1 else a
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int) returns (result: int)
    requires ValidInput(a, b)
    ensures result == TakahashiCount(a, b)
    ensures a > b ==> result == a - 1
    ensures a <= b ==> result == a
// </vc-spec>
// <vc-code>
{
    if a > b {
        result := a - 1;
    } else {
        result := a;
    }
}
// </vc-code>

