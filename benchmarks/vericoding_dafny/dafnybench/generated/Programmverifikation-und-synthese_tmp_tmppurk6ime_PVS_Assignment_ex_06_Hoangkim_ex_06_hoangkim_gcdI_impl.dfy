// The recursive `gcd` function works by:
// 
// I need to implement this iteratively while maintaining the invariant that the GCD of the current values equals the GCD of the original inputs.

//Problem01
//a)
ghost function gcd(x: int, y: int): int
    requires x > 0 && y > 0
{
    if x == y then x
    else if x > y then gcd(x - y, y)
    else gcd(x, y - x)
}

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method gcdI(m: int, n: int) returns (d: int)
requires  m > 0 && n > 0 
ensures d == gcd(m, n);
// </vc-spec>
// <vc-code>
{
  var x := m;
  var y := n;
  
  while x != y
    invariant x > 0 && y > 0
    invariant gcd(x, y) == gcd(m, n)
    decreases x + y
  {
    if x > y {
      x := x - y;
    } else {
      y := y - x;
    }
  }
  
  d := x;
}
// </vc-code>

//b)
ghost function gcd'(x: int, y: int): int
    requires x > 0 && y > 0
    decreases if x > y then x else y
{
    if x == y then x
    else if x > y then gcd'(x - y, y)
    else gcd(y, x)
}