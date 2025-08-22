// ATOM 
function Power(n: nat): nat {
    if n == 0 then 1 else 2 * Power(n - 1)
}

// IMPL 
method ComputePower(N: int) returns (y: nat) 
    requires N >= 0
    ensures y == Power(N)
{
    if N == 0 {
        y := 1;
    } else {
        var temp := ComputePower(N - 1);
        y := 2 * temp;
    }
}