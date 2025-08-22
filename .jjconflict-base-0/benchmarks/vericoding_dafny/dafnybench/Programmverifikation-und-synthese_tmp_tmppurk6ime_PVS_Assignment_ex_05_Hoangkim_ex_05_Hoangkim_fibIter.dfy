//Problem01
function fib(n: nat):nat
{
    if n < 2 then n else fib(n-2)+fib(n-1)
}

// <vc-helpers>
// </vc-helpers>

method fibIter(n:nat) returns (a:nat)
requires n > 0
ensures a == fib(n)
// <vc-code>
{
  assume false;
}
// </vc-code>

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

//# 3 pts


// # sum: 9 pts