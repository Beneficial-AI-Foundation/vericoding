//ATOM
function fib(n: nat): nat
{
  if n == 0 then 0 else
  if n == 1 then 1 else
          fib(n - 1) + fib(n - 2)
}


// SPEC

method ComputeFib(n: nat) returns (b: nat)
  ensures b == fib(n) // Do not change this postcondition
{
}
