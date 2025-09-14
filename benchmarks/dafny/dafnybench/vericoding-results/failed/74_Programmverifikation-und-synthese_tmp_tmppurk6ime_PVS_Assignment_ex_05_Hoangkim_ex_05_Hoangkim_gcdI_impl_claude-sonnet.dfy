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
lemma gcdPreservation(m: nat, n: nat, m': nat, n': nat)
    requires m > 0 && n > 0 && m' > 0 && n' > 0
    requires gcd(m, n) == gcd(m', n')
    ensures gcd(m, n) == gcd(m', n')
{
}

lemma gcdSubtraction(m: nat, n: nat)
    requires m > 0 && n > 0 && m > n
    ensures gcd(m, n) == gcd(m - n, n)
{
}

lemma gcdSubtractionSymmetric(m: nat, n: nat)
    requires m > 0 && n > 0 && n > m
    ensures gcd(m, n) == gcd(m, n - m)
{
}
// </vc-helpers>

// <vc-spec>
method gcdI(m: int, n: int) returns (g: int)
    requires  m > 0 && n > 0 
    ensures g == gcd(m, n);
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