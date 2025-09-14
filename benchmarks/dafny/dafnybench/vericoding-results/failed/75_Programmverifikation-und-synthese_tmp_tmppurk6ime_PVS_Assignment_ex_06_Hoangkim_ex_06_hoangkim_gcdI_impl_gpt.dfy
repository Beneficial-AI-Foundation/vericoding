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
lemma unfold_gcd(x: int, y: int)
  requires x > 0 && y > 0
  ensures gcd(x, y) == (if x == y then x else if x > y then gcd(x - y, y) else gcd(x, y - x))
{
  reveal gcd();
}
// </vc-helpers>

// <vc-spec>
method gcdI(m: int, n: int) returns (d: int)
requires  m > 0 && n > 0 
ensures d == gcd(m, n);
// </vc-spec>
// <vc-code>
{
  var a := m;
  var b := n;
  while a != b
    invariant a > 0 && b > 0
    invariant gcd(a, b) == gcd(m, n)
    decreases a + b
  {
    if a > b {
      unfold_gcd(a, b);
      assert gcd(a, b) == gcd(a - b, b);
      assert gcd(a - b, b) == gcd(m, n);
      a := a - b;
    } else {
      unfold_gcd(a, b);
      assert gcd(a, b) == gcd(a, b - a);
      assert gcd(a, b - a) == gcd(m, n);
      b := b - a;
    }
  }
  unfold_gcd(a, b);
  assert gcd(a, b) == a;
  d := a;
}
// </vc-code>

