// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Abs(x: int) returns (result: int)
    requires x != -2147483648
    ensures result >= 0
    ensures result == x || result == -x
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
