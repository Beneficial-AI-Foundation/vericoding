// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Triple(x: int) returns (result: int)
    ensures result / 3 == x
    ensures result / 3 * 3 == result
// </vc-spec>
// <vc-code>
{
    result := 3 * x;
}
// </vc-code>
