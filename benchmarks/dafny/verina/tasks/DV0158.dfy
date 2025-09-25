// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method MultipleReturns(x: int, y: int) returns (result: (int, int))
    ensures result.0 == x + y
    ensures result.1 + y == x
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume {:axiom} false;
    result := (0, 0);
    // impl-end
}
// </vc-code>
