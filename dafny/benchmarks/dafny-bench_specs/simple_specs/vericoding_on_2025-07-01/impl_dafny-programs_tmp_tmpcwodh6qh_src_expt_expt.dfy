//ATOM
function Expt(b: int, n: nat): int
 requires n >= 0
{
 if n == 0 then 1 else b * Expt(b, n - 1)
}

//IMPL
method expt(b: int, n: nat) returns (res: int) 
 ensures res == Expt(b, n)
{
    if n == 0 {
        res := 1;
    } else {
        res := 1;
        var i := 0;
        while i < n
            invariant 0 <= i <= n
            invariant res == Expt(b, i)
        {
            res := res * b;
            i := i + 1;
        }
    }
}