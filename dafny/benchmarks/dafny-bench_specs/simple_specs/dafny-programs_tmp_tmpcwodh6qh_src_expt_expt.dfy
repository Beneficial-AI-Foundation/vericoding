//ATOM
function Expt(b: int, n: nat): int
 requires n >= 0
{
 if n == 0 then 1 else b * Expt(b, n - 1)
}


// SPEC

method expt(b: int, n: nat) returns (res: int) 
 ensures res == Expt(b, n)
{
}
