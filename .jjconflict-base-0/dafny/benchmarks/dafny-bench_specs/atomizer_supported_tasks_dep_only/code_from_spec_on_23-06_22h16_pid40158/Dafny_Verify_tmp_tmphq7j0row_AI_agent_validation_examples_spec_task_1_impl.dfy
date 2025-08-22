// ATOM 
function Power(n: nat): nat {
    if n == 0 then 1 else 2 * Power(n - 1)
}

//IMPL 
method ComputePower(N: int) returns (y: nat) 
    requires N >= 0
    ensures y == Power(N)
{
    y := 1;
    var x := 0;
    while x != N
        decreases N - x
        invariant 0 <= x <= N
        invariant y == Power(x)
    {
        y := y * 2;
        x := x + 1;
    }
}