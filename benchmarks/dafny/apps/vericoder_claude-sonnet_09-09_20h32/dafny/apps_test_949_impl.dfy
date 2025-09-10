predicate ValidInput(a: int, b: int)
{
    1 <= a <= b
}

function GcdOfRange(a: int, b: int): int
    requires ValidInput(a, b)
{
    if a == b then a else 1
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int) returns (result: int)
    requires ValidInput(a, b)
    ensures result == GcdOfRange(a, b)
    ensures a == b ==> result == a
    ensures a < b ==> result == 1
// </vc-spec>
// <vc-code>
{
    if a == b {
        result := a;
    } else {
        result := 1;
    }
}
// </vc-code>

