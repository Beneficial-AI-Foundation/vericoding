//ATOM

//Problem01
function fib(n: nat):nat
{
  if n < 2 then n else fib(n-2)+fib(n-1)
}


// SPEC

method fibIter(n:nat) returns (a:nat)
requires n > 0
ensures a == fib(n)
{
}