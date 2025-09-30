// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method multiply(a: int, b: int) returns (result: int)
    ensures result == a * b
// </vc-spec>
// <vc-code>
{
    result := a * b;
}
// </vc-code>
