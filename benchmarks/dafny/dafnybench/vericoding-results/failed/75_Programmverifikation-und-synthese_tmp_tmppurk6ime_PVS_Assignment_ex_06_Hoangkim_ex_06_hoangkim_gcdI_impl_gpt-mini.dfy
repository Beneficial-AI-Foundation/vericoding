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
lemma gcd_sub(x: int, y: int)
  requires x > 0 && y > 0 && x > y
  ensures gcd(x, y) == gcd(x - y, y)
{
  assert gcd(x, y) == gcd(x - y, y)
}

lemma gcd_diag(x: int)
  requires x > 0
  ensures gcd(x, x) == x
{
  assert gcd(x, x) == x
}
// </vc-helpers>

// <vc-spec>
method gcdI(m: int, n: int) returns (d: int)
requires  m > 0 && n > 0 
ensures d == gcd(m, n);
// </vc-spec>
// <vc-code>
{
  var a := m
  var b := n
  while a != b
    invariant a > 0 && b > 0
    invariant gcd(a, b) == gcd(m, n)
    decreases a + b
  {
    if a > b {
      gcd_sub(a, b)
      a := a - b
    } else {
      gcd_sub(b, a)
      b := b - a
    }
  }
  assert a == b
  assert gcd(a, a) == gcd(a, b)
  assert gcd(a, b) == gcd(m, n)
  d := a
  gcd_diag(d)
  assert gcd(d, d) == d
  assert gcd(d, d) == gcd(m, n)
  assert d == gcd(m, n)
}
// </vc-code>

