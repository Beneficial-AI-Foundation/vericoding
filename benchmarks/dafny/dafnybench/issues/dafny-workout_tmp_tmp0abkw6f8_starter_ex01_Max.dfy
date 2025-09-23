// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method Max(a: int, b: int) returns (c: int)
    ensures c >= a && c >= b && (c == a || c == b)
// </vc-spec>
// <vc-code>
{
    if (a >= b)
    {
        return a;
    } else {
        return b;
    }
}
// </vc-code>
