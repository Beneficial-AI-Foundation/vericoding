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
lemma GcdCommutes(x: int, y: int)
  requires x > 0 && y > 0
  decreases x + y
  ensures gcd(x, y) == gcd(y, x)
{
  if x != y {
    if x > y {
      GcdSubtract(x, y);
      GcdCommutes(x - y, y);
    } else {
      GcdSubtract(y, x);
      GcdCommutes(x, y - x);
    }
  }
}

lemma GcdSubtract(x: int, y: int)
  requires x > 0 && y > 0 && x != y
  decreases x + y
  ensures gcd(x, y) == (if x > y then gcd(x - y, y) else gcd(x, y - x))
{
  // Dafny automatically proves this property for the ghost function
}

lemma GcdEqual(a: int, b: int)
  requires a > 0 && b > 0
  requires a == b
  ensures gcd(a, b) == a
{
}
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

