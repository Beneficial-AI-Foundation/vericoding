//Problem01
// <vc-spec>
function fib(n: nat):nat
{
    if n < 2 then n else fib(n-2)+fib(n-1)
}

//# 2 pts

//Problem02
function fact(n:nat):nat
{if n==0 then 1 else n*fact(n-1)}

// <vc-helpers>
lemma factMultiplicative(k: nat, n: nat)
    requires k <= n
    ensures fact(n) == fact(k) * factRange(k + 1, n)

function factRange(start: nat, end: nat): nat
    requires start <= end + 1
    decreases end + 1 - start
{
    if start > end then 1
    else start * factRange(start + 1, end)
}

lemma factRangeCorrect(k: nat, n: nat)
    requires k <= n
    ensures fact(n) == fact(k) * factRange(k + 1, n)
    decreases n - k
{
    if k == n {
        assert factRange(k + 1, n) == factRange(n + 1, n) == 1;
    } else {
        factRangeCorrect(k + 1, n);
        assert fact(n) == fact(k + 1) * factRange(k + 2, n);
        assert fact(k + 1) == (k + 1) * fact(k);
        assert factRange(k + 1, n) == (k + 1) * factRange(k + 2, n);
    }
}
// </vc-helpers>

method factIter(n:nat) returns (a:nat)
requires n >= 0
ensures a == fact(n)
// </vc-spec>
// <vc-code>
{
    a := 1;
    var i := 0;
    
    while i < n
        invariant 0 <= i <= n
        invariant a == fact(i)
    {
        i := i + 1;
        a := a * i;
    }
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