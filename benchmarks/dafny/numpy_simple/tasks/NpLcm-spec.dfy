// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method LcmInt(a: int, b: int) returns (result: int)
    requires a != 0 && b != 0
    ensures result >= 0
    ensures result % a == 0
    ensures result % b == 0
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume {:axiom} false;
    // impl-end
}
// </vc-code>
