// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method DoubleQuadruple(x: int) returns (result: (int, int))
    ensures result.0 == 2 * x
    ensures result.1 == 2 * result.0
// </vc-spec>
// <vc-code>
{
    result := (2 * x, 4 * x);
}
// </vc-code>
