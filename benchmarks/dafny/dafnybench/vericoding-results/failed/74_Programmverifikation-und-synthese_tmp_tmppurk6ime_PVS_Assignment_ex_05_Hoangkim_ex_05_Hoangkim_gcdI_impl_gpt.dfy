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
  while a != b
    invariant a > 0 && b > 0
    invariant gcd(a, b) == gcd(m, n)
    decreases a + b
  {
    if a > b {
      assert gcd(a, b) == gcd(a - b, b);
      a := a - b;
    } else {
      assert gcd(a, b) == gcd(a, b - a);
      b := b - a;
    }
  }
  g := a;
  assert a == b;
  assert gcd(a, a) == gcd(a, b);
  assert gcd(a, b) == gcd(m, n);
  assert gcd(a, a) == gcd(m, n);
  assert gcd(a, a) == a;
}
// </vc-code>

//# 3 pts


// # sum: 9 pts