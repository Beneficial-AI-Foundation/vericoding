// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method Max(a: int, b: int) returns (maxValue: int)
    ensures maxValue == a || maxValue == b
    ensures maxValue >= a && maxValue >= b
// </vc-spec>
// <vc-code>
{
    if a >= b {
        maxValue := a;
    } else {
        maxValue := b;
    }
}
// </vc-code>
