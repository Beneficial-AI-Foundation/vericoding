// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function min(x: int, y: int): int {
    if x < y then x else y
}
// </vc-helpers>

// <vc-spec>
method MyMin(a: int, b: int) returns (result: int)
    ensures result <= a && result <= b
    ensures result == a || result == b
// </vc-spec>
// <vc-code>
{
    result := min(a, b);
}
// </vc-code>
