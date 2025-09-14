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
lemma gcd_sub_left(m: nat, n: nat)
  requires m > n && n > 0
  ensures gcd(m - n, n) == gcd(m, n)
  decreases m + n
{
  // Unfold the definition of gcd for the case m > n.
  // By the function definition, gcd(m, n) == gcd(m - n, n).
  if m == n {
    // This branch cannot occur because requires m > n.
    assert false;
  } else if m > n {
    // By definition of gcd when m > n.
    assert gcd(m, n) == gcd(m - n, n);
  } else {
    // This branch cannot occur because requires m > n.
    assert false;
  }
}

lemma gcd_comm(m: nat, n: nat)
  requires m > 0 && n > 0
  ensures gcd(m, n) == gcd(n, m)
  decreases m + n
{
  if m == n {
    // trivial: gcd(m,m) == m == gcd(m,m)
  } else if m > n {
    // gcd(m, n) == gcd(m - n, n)
    assert gcd(m, n) == gcd(m - n, n);
    // Apply induction on smaller pair (m-n, n)
    gcd_comm(m - n, n);
    // Now gcd(m - n, n) == gcd(n, m - n) by induction
    assert gcd(m - n, n) == gcd(n, m - n);
    // And by definition when m > n, gcd(n, m) == gcd(n, m - n)
    assert gcd(n, m) == gcd(n, m - n);
    // Transitivity
    assert gcd(m, n) == gcd(n, m);
  } else {
    // n > m
    assert gcd(m, n) == gcd(m, n - m);
    gcd_comm(m, n - m);
    assert gcd(m, n - m) == gcd(n - m, m);
    assert gcd(n, m) == gcd(n - m, m);
    assert gcd(m, n) == gcd(n, m);
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
  var a := m as nat;
  var b := n as nat;
  while a != b
    invariant a > 0 && b > 0 && gcd(a, b) == gcd(m as nat, n as nat)
    decreases a + b
  {
    if a > b {
      gcd_sub_left(a, b);
      a := a - b;
    } else {
      // here b > a
      gcd_sub_left(b, a);
      b := b - a;
    }
  }
  g := a as int;
}
// </vc-code>

//# 3 pts


// # sum: 9 pts