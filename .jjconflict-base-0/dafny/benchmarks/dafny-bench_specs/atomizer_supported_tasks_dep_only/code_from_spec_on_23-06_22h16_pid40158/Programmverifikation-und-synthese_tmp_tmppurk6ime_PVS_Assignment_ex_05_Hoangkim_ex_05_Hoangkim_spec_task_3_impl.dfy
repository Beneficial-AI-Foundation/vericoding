//Problem01
//ATOM fib
function fib(n: nat): nat
{
    if n <= 1 then n
    else fib(n-1) + fib(n-2)
}

//ATOM fibIter
method fibIter(n: nat) returns (result: nat)
    ensures result == fib(n)
{
    if n <= 1 {
        result := n;
    } else {
        var a := 0;
        var b := 1;
        var i := 2;
        while i <= n
            invariant 2 <= i <= n + 1
            invariant a == fib(i-2)
            invariant b == fib(i-1)
        {
            var temp := a + b;
            a := b;
            b := temp;
            i := i + 1;
        }
        result := b;
    }
}

//Problem02
//ATOM fact
function fact(n: nat): nat
{
    if n == 0 then 1
    else n * fact(n-1)
}

//ATOM factIter
method factIter(n: nat) returns (result: nat)
    ensures result == fact(n)
{
    result := 1;
    var i := 1;
    while i <= n
        invariant 1 <= i <= n + 1
        invariant result == fact(i-1)
    {
        result := result * i;
        i := i + 1;
    }
}

//Problem03
//ATOM gcd
function gcd(m: nat, n: nat): nat
    requires m > 0 && n > 0
{
    if m == n then m
    else if m > n then gcd(m - n, n)
    else gcd(m, n - m)
}

//IMPL gcdI
method gcdI(m: int, n: int) returns (g: int)
    requires m > 0 && n > 0 
    ensures g == gcd(m, n)
{
    /* code modified by LLM (iteration 1): Convert int parameters to nat variables for proper type handling */
    var a: nat := m;
    var b: nat := n;
    while a != b
        invariant a > 0 && b > 0
        invariant gcd(a, b) == gcd(m, n)
    {
        if a > b {
            a := a - b;
        } else {
            b := b - a;
        }
    }
    /* code modified by LLM (iteration 1): Assign result directly since nat is subtype of int */
    g := a;
}