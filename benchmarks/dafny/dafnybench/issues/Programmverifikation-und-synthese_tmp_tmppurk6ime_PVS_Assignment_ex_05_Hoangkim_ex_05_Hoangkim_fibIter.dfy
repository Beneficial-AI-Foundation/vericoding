// <vc-preamble>
//Problem01
function fib(n: nat):nat
{
    if n < 2 then n else fib(n-2)+fib(n-1)
}
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method fibIter(n:nat) returns (a:nat)
requires n > 0
ensures a == fib(n)
// </vc-spec>
// <vc-code>
{
    a := 0;
    var b,x := 1,0;
    while x < n 
        invariant 0 <= x <= n
        invariant a == fib(x)
        invariant b == fib(x+1)
        {
            a,b := b,a+b;
            //why a,b := b,a+b is okay
            //but when I write  a := b;      //# Because this  
            //                  b := a+b;    //# is not the same  !! 
            //is error?                      //# {a = 1 , b = 2 } a := b ; b := a+b { b = 4 }, but 
            x := x+1;                        //# {a = 1 , b = 2 }   a, b := b,a+b  { b = 3 }
        }
    assert a == fib(n);     
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