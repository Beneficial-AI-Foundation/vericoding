// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
method SwapArithmetic_Helper(a: int, b: int) returns (x: int, y: int)
    ensures x == b
    ensures y == a
{
    x := b;
    y := a;
}
// </vc-helpers>

// <vc-spec>
method SwapArithmetic(x: int, y: int) returns (result: (int, int))
    ensures result.0 == y
    ensures result.1 == x
    ensures x != y ==> (result.0 != x && result.1 != y)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Fixed invalid assignments to parameters, use local variables instead */
    var x_copy := x;
    var y_copy := y;
    x_copy := x_copy + y_copy;
    y_copy := x_copy - y_copy;
    x_copy := x_copy - y_copy;
    result := (x_copy, y_copy);
}
// </vc-code>
