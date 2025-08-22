//ATOM

function gcd(m: nat, n: nat) : nat
requires m>0 && n>0
{
  if(m==n) then n 
  else if( m > n) then gcd(m-n,n)
  else gcd(m, n-m)
}


// SPEC

method gcdCalc(m: nat, n: nat) returns (res: nat)
requires m>0 && n>0
ensures res == gcd(m,n)
{
}
