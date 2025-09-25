// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Triple(x: int) returns (result: int)
    ensures result == 3 * x
// </vc-spec>
// <vc-code>
{
    // impl-start
    result := 3 * x;
    // impl-end
}
// </vc-code>
