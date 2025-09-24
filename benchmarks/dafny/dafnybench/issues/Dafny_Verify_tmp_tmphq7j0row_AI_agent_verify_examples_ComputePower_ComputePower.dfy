// <vc-preamble>
function Power(n: nat): nat {
    if n == 0 then 1 else 2 * Power(n - 1)
}
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method ComputePower(N: int) returns (y: nat) requires N >= 0
    ensures y == Power(N)
// </vc-spec>
// <vc-code>
{
    y := 1;
    var x := 0; 
    while x != N
        invariant 0 <= x <= N 
        invariant y == Power(x) 
        decreases N - x
    {
        x, y := x + 1, y + y;
    } 
}
// </vc-code>
