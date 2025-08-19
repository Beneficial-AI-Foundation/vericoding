//ATOM

function gcd(m: nat, n: nat) : nat
requires m>0 && n>0
{
  if(m==n) then n 
  else if( m > n) then gcd(m-n,n)
  else gcd(m, n-m)
}


//IMPL 

method gcdCalc(m: nat, n: nat) returns (res: nat)
requires m>0 && n>0
ensures res == gcd(m,n)
{
  var a := m;
  var b := n;
  
  while a != b
    invariant a > 0 && b > 0
    invariant gcd(a, b) == gcd(m, n)
    decreases a + b
  {
    if a > b {
      a := a - b;
    } else {
      b := b - a;
    }
  }
  
  res := a;
}