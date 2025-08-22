//Problem01
//ATOM fib
function fib(n: nat): nat
{
    if n <= 1 then n else fib(n-1) + fib(n-2)
}

//ATOM fibIter
method fibIter(n: nat) returns (result: nat)
    ensures result == fib(n)
{
    if n <= 1 {
        result := n;
        return;
    }
    
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

//# 2 pts

//Problem02
// ATOM 
//# 2 pts

//Problem02
function fact(n:nat):nat
{if n==0 then 1 else n*fact(n-1)}

//IMPL factIter
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
        /* code modified by LLM (iteration 1): increment i first, then multiply by new i value to maintain invariant a == fact(i) */
        i := i + 1;
        a := a * i;
    }
}
 
//# 3 pts
//Problem03
//ATOM gcd
function gcd(a: nat, b: nat): nat
{
    if b == 0 then a else gcd(b, a % b)
}

//ATOM gcdI
method gcdI(a: nat, b: nat) returns (result: nat)
    ensures result == gcd(a, b)
{
    var x := a;
    var y := b;
    
    while y != 0
        invariant gcd(x, y) == gcd(a, b)
        decreases y
    {
        var temp := x % y;
        x := y;
        y := temp;
    }
    
    result := x;
}

//# 3 pts

// # sum: 9 pts