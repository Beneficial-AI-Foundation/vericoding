//ATOM

function F(n: nat): nat { if n <= 2 then n else F(n-1) + F(n-3)}


// SPEC

method calcF(n: nat) returns (res: nat) 
 ensures res == F(n) 
{
}