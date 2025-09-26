// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method Abs2(x: real) returns (y: real)
    requires x == -0.5
    ensures 0.0 <= y
    ensures 0.0 <= x ==> y == x
    ensures x < 0.0 ==> y == -x
// </vc-spec>
// <vc-code>
{
    return x + 1.0;
}
// </vc-code>
