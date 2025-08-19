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
  /* code modified by LLM (iteration 1): Changed variable types to nat to match gcd function requirements */
  var a: nat := m;
  var b: nat := n;
  
  while a != b
    /* code modified by LLM (iteration 1): Strengthened invariant to help prove termination */
    invariant a > 0 && b > 0
    invariant gcd(a, b) == gcd(m, n)
    invariant a <= m + n && b <= m + n
    decreases a + b
  {
    if a > b {
      a := a - b;
    } else {
      b := b - a;
    }
  }
  
  g := a;
}