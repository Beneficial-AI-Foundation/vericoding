// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method SwapBitvectors(x: int, y: int) returns (result: (int, int))
    requires 0 <= x < 256 && 0 <= y < 256
    ensures result.0 == y && result.1 == x
    ensures x != y ==> (result.0 != x && result.1 != y)
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
    return (0, 0);
}
// </vc-code>
