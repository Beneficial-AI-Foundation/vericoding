//ATOM
function Power(n: nat): nat {
  if n == 0 then 1 else 2 * Power(n - 1)
}


// SPEC

method ComputePower(N: int) returns (y: nat) requires N >= 0
  ensures y == Power(N)
{
}
