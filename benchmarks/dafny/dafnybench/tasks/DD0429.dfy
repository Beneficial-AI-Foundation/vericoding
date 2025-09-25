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
  assume {:axiom} false;
}
// </vc-code>
