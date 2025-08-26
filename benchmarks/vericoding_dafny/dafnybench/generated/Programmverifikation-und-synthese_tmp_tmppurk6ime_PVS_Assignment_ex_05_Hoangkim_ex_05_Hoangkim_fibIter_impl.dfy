// - The method `fibIter` takes a natural number `n > 0`
// - It should return `fib(n)` computed iteratively
// - I need to maintain loop invariants to prove correctness

// I'll use the standard iterative approach with two variables tracking consecutive Fibonacci numbers, and use a loop invariant to prove the implementation matches the recursive specification.

//Problem01
// <vc-spec>
function fib(n: nat):nat
{
    if n < 2 then n else fib(n-2)+fib(n-1)
}

// <vc-helpers>
// </vc-helpers>

method fibIter(n:nat) returns (a:nat)
requires n > 0
ensures a == fib(n)
// </vc-spec>
// <vc-code>
{
  if n == 1 {
    a := 1;
  } else {
    var prev := 0;
    var curr := 1;
    var i := 2;
    
    while i <= n
      invariant 2 <= i <= n + 1
      invariant prev == fib(i - 2)
      invariant curr == fib(i - 1)
    {
      var temp := curr;
      curr := prev + curr;
      prev := temp;
      i := i + 1;
    }
    
    a := curr;
  }
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