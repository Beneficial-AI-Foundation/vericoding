//Problem01
function fib(n: nat):nat
{
    if n < 2 then n else fib(n-2)+fib(n-1)
}

//# 2 pts

//Problem02
function fact(n:nat):nat
{if n==0 then 1 else n*fact(n-1)}

//# 3 pts
//Problem03
function gcd(m: nat, n: nat): nat
    requires m > 0 && n > 0
{
    if m == n then m
    else if m > n then gcd(m - n, n)
    else gcd(m, n - m)
}

// <vc-helpers>
lemma gcd_symmetric(m: nat, n: nat)
  requires m > 0 && n > 0
  ensures gcd(m, n) == gcd(n, m)
{
}

lemma gcd_zero(a: nat)
  requires a > 0
  ensures gcd(a, a) == a
{
}

lemma gcd_subtract_property(m: nat, n: nat)
  requires m > 0 && n > 0
  ensures m > n ==> gcd(m, n) == gcd(m - n, n)
  ensures n > m ==> gcd(m, n) == gcd(m, n - m)
{
}

lemma gcd_stable(m: nat, n: nat, a: nat, b: nat)
  requires m > 0 && n > 0 && a > 0 && b > 0
  requires gcd(a, b) == gcd(m, n)
  ensures gcd(m, n) == gcd(if a > b then a - b else a, if a > b then b else b - a)
{
  if a > b {
    gcd_subtract_property(a, b);
    assert gcd(a, b) == gcd(a - b, b);
  } else if b > a {
    gcd_subtract_property(a, b);
    assert gcd(a, b) == gcd(a, b - a);
  } else {
    // When a == b, both sides are gcd(a, b)
  }
}
// </vc-helpers>

// <vc-spec>
method gcdI(m: int, n: int) returns (g: int)
    requires  m > 0 && n > 0 
    ensures g == gcd(m, n);
// </vc-spec>
// <vc-code>
{
  var a: nat := m;
  var b: nat := n;
  
  while (a != b)
    decreases a + b
    invariant a > 0 && b > 0
    invariant gcd(a, b) == gcd(m, n)
  {
    gcd_stable(m, n, a, b);
    if (a > b) {
      a := a - b;
    } else if (b > a) {
      b := b - a;
    }
  }
  
  g := a;
  assert gcd(a, b) == a by {
    gcd_zero(a);
  };
}
// </vc-code>

//# 3 pts


// # sum: 9 pts