// <vc-preamble>
function fib(n: nat):nat
{
    if n < 2 then n else fib(n-2)+fib(n-1)
}

function fact(n:nat):nat
{if n==0 then 1 else n*fact(n-1)}

function gcd(m: nat, n: nat): nat
    requires m > 0 && n > 0
{
    if m == n then m
    else if m > n then gcd(m - n, n)
    else gcd(m, n - m)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method gcdI(m: int, n: int) returns (g: int)
    requires  m > 0 && n > 0 
    ensures g == gcd(m, n);
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Fixed if-statement syntax and removed deprecated semicolons */
  var a : nat := m as nat;
  var b : nat := n as nat;
  while (a != b)
    invariant a > 0 && b > 0
    invariant gcd(a, b) == gcd(m as nat, n as nat)
    decreases a + b
  {
    if a > b {
      a := a - b;
    } else {
      b := b - a;
    }
  }
  g := a as int;
}
// </vc-code>
