// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function max(x: int, y: int): int { if x >= y then x else y }
// </vc-helpers>

// <vc-spec>
method MaxOfThree(a: int, b: int, c: int) returns (result: int)
    ensures result >= a && result >= b && result >= c
    ensures result == a || result == b || result == c
// </vc-spec>
// <vc-code>
{
    var maxAB := max(a, b);
    result := max(maxAB, c);
}
// </vc-code>
