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
lemma GcdDecreases(m: nat, n: nat)
    requires m > 0 && n > 0
    ensures m != n ==> gcd(m, n) == (if m > n then gcd(m - n, n) else gcd(m, n - m))
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method gcdI(m: int, n: int) returns (g: int)
    requires  m > 0 && n > 0 
    ensures g == gcd(m, n);
// </vc-spec>
// </vc-spec>

// <vc-code>
method GcdImpl(m: int, n: int) returns (g: int)
    requires m > 0 && n > 0
    ensures g == gcd(m, n)
{
    var a: nat := m;
    var b: nat := n;
    while a != b
        decreases if a > b then a else b
        invariant a > 0 && b > 0
        invariant gcd(a, b) == gcd(m, n)
    {
        if a > b {
            a := a - b;
        } else {
            b := b - a;
        }
    }
    g := a;
}
// </vc-code>

//# 3 pts


// # sum: 9 pts