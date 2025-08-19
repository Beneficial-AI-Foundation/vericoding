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

//IMPL
method gcdI(m: int, n: int) returns (g: int)
  requires m > 0 && n > 0 
  ensures g == gcd(m, n)
{
  var a := m;
  var b := n;
  
  while a != b
    invariant a > 0 && b > 0
    invariant gcd(a, b) == gcd(m, n)
  {
    if a > b {
      a := a - b;
    } else {
      b := b - a;
    }
  }
  
  g := a;
}