//IMPL Problem01
function fib(n: nat):nat
{
    if n < 2 then n else fib(n-2)+fib(n-1)
}

method fibIter(n:nat) returns (a:nat)
requires n > 0
ensures a == fib(n)
{
    /* code modified by LLM (iteration 4): Fixed base case handling and loop condition */
    if n == 1 {
        a := 1;
    } else {
        var prev := 0;  // fib(0)
        var curr := 1;  // fib(1)
        var i := 2;
        
        while i <= n
            invariant 2 <= i <= n + 1
            invariant prev == fib(i - 2)
            invariant curr == fib(i - 1)
        {
            var next := prev + curr;
            prev := curr;
            curr := next;
            i := i + 1;
        }
        a := curr;
    }
}

//IMPL Problem02
function fact(n:nat):nat
{if n==0 then 1 else n*fact(n-1)}

method factIter(n:nat) returns (a:nat)
requires n >= 0;
ensures a == fact(n)
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

//IMPL Problem03
function gcd(m: nat, n: nat): nat
    requires m > 0 && n > 0
{
    if m == n then m
    else if m > n then gcd(m - n, n)
    else gcd(m, n - m)
}

method gcdI(m: int, n: int) returns (g: int)
    requires  m > 0 && n > 0 
    ensures g == gcd(m, n);
{
    /* code modified by LLM (iteration 1): Added type conversion for nat compatibility */
    var a := m as nat;
    var b := n as nat;
    
    while a != b
        invariant a > 0 && b > 0
        invariant gcd(a, b) == gcd(m as nat, n as nat)
    {
        if a > b {
            a := a - b;
        } else {
            b := b - a;
        }
    }
    g := a as int;
}