//ATOM gcd_function
//b)
ghost function gcd'(x: int, y: int): int
  requires x > 0 && y > 0
{
  if x == y then x
  else if x > y then gcd'(x - y, y)
  else gcd'(y, x)
}

//IMPL gcdI
method gcdI(m: int, n: int) returns (d: int)
requires m > 0 && n > 0 
ensures d == gcd'(m, n)
{
  var a := m;
  var b := n;
  
  while a != b
    invariant a > 0 && b > 0
    invariant gcd'(a, b) == gcd'(m, n)
    /* code modified by LLM (iteration 1): Changed decreases clause to use max(a,b) for proper termination proof */
    decreases if a >= b then a else b
  {
    if a > b {
      a := a - b;
    } else {
      b := b - a;
    }
  }
  
  d := a;
}