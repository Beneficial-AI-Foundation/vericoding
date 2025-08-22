//ATOM
//# 3 pts
//Problem03
function gcd(m: nat, n: nat): nat
  requires m > 0 && n > 0
{
  if m == n then m
  else if m > n then gcd(m - n, n)
  else gcd(m, n - m)
}


// SPEC

method gcdI(m: int, n: int) returns (g: int)
  requires m > 0 && n > 0 
  ensures g == gcd(m, n)
  {
}
