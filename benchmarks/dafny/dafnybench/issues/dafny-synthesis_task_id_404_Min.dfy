// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method Min(a: int, b: int) returns (minValue: int)
    ensures minValue == a || minValue == b
    ensures minValue <= a && minValue <= b
// </vc-spec>
// <vc-code>
{
    if a <= b {
        minValue := a;
    } else {
        minValue := b;
    }
}
// </vc-code>
