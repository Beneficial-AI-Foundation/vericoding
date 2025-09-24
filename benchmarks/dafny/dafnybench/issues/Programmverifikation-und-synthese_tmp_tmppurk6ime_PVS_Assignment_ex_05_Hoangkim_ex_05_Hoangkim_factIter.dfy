// <vc-preamble>
//Problem01
function fib(n: nat):nat
{
    if n < 2 then n else fib(n-2)+fib(n-1)
}

//# 2 pts

//Problem02
function fact(n:nat):nat
{if n==0 then 1 else n*fact(n-1)}
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method factIter(n:nat) returns (a:nat)
requires n >= 0;
ensures a == fact(n)
// </vc-spec>
// <vc-code>
{
    a := 1;
    var i := 1;
    while i <= n
        invariant 1 <= i <= n+1
        invariant a == fact(i-1)
    {
        a := a * i;
        i := i + 1;
    }
    assert a == fact(n);
}
// </vc-code>

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