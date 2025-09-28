// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
method MultipleReturnsHelper(x: int, y: int) returns (result: (int, int))
    ensures result.0 == x + y
    ensures result.1 + y == x
{
    result := (x + y, x - y);
}
// </vc-helpers>

// <vc-spec>
method MultipleReturns(x: int, y: int) returns (result: (int, int))
    ensures result.0 == x + y
    ensures result.1 + y == x
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): call helper function */
    result := MultipleReturnsHelper(x, y);
}
// </vc-code>
