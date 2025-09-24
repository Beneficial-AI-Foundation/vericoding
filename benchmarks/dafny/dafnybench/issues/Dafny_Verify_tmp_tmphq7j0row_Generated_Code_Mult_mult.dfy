// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method mult(a:int, b:int) returns (x:int)
    requires a >= 0 && b >= 0
    ensures x == a * b
// </vc-spec>
// <vc-code>
{
    x := 0;
    var y := a;
    while y > 0
        invariant x == (a - y) * b
    {
        x := x + b;
        y := y - 1;
    }
}
// </vc-code>
