// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
method DoubleQuadrupleHelper(x: int) returns (result: (int, int))
    ensures result.0 == 2 * x
    ensures result.1 == 2 * result.0
{
    result := (2 * x, 4 * x);
}
// </vc-helpers>

// <vc-spec>
method DoubleQuadruple(x: int) returns (result: (int, int))
    ensures result.0 == 2 * x
    ensures result.1 == 2 * result.0
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): call renamed helper method */
    result := DoubleQuadrupleHelper(x);
}
// </vc-code>
