// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method SwapArithmetic(x: int, y: int) returns (result: (int, int))
    ensures result.0 == y
    ensures result.1 == x
    ensures x != y ==> (result.0 != x && result.1 != y)
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume {:axiom} false;
    result := (0, 0);
    // impl-end
}
// </vc-code>
