// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method Abs(x: int) returns (y: int)
    requires x < 0
    ensures 0 < y
    ensures y == -x
// </vc-spec>
// <vc-code>
{
    return -x;
}
// </vc-code>
