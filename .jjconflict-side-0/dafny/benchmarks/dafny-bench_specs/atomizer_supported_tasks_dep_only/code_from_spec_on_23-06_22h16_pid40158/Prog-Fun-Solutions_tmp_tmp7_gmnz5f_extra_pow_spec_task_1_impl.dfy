// ATOM 
ghost function pow(a: int, e: nat): int {
    if e == 0 then 1 else a*pow(a, e-1)
}

// IMPL 
method Pow(a: nat, n: nat) returns (y: nat)
ensures y == pow(a, n)
{
    if n == 0 {
        y := 1;
    } else {
        y := a;
        var i := 1;
        while i < n
            invariant 1 <= i <= n
            invariant y == pow(a, i)
        {
            y := y * a;
            i := i + 1;
        }
    }
}