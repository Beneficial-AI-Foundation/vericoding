//ATOM

function C(n: nat): nat 
{
  if n == 0 then 1 else (4 * n - 2) * C(n-1) / (n + 1) 
}


// SPEC

method calcC(n: nat) returns (res: nat)
  ensures res == C(n)
{
}