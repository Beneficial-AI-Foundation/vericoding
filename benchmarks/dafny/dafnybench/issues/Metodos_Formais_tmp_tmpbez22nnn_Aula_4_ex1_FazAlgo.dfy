// <vc-preamble>
predicate Par(n:int)
{
    n % 2 == 0
}
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method FazAlgo (a:int, b:int) returns (x:int, y:int)
requires a >= b && Par (a-b)
// </vc-spec>
// <vc-code>
{
    x := a;
    y := b;
    while x != y
    invariant x >= y
    invariant Par(x-y)
    decreases x-y
    {
        x := x - 1;
        y := y + 1;
    }
}
// </vc-code>
