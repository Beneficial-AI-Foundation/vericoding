//Problem01
//a)
ghost function gcd(x: int, y: int): int
    requires x > 0 && y > 0
{
    if x == y then x
    else if x > y then gcd(x - y, y)
    else gcd(x, y - x)
}

//b)
ghost function gcd'(x: int, y: int): int
    requires x > 0 && y > 0
    decreases if x > y then x else y
{
    if x == y then x
    else if x > y then gcd'(x - y, y)
    else gcd(y, x)
}

// <vc-helpers>
ghost function gcd(x: int, y: int): int
  requires x >= 0 && y >= 0
  decreases y
  ensures if y == 0 then d == x else d == gcd(y, x % y)
  ensures d >= 0
  ensures forall k :: k > 0 && x % k == 0 && y % k == 0 ==> d % k == 0 // k divides d when d is multiple of k
{ if y == 0 then x else gcd(y, x % y) }
// </vc-helpers>

// <vc-spec>
method gcdI(m: int, n: int) returns (d: int)
requires  m > 0 && n > 0 
ensures d == gcd(m, n);
// </vc-spec>
// <vc-code>
{ var a := m;
  var b := n;
  while b != 0
    invariant 0 < a && 0 <= b && gcd(a, b) == gcd(m, n)
  { var temp := b;
    b := a % b;
    a := temp;
  }
  d := a; }
// </vc-code>

