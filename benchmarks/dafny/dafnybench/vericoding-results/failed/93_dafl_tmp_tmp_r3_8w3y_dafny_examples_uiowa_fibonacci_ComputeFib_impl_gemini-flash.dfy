/*
   CS:5810 Formal Methods in Software Engineering
   Fall 2017
   The University of Iowa

   Instructor: Cesare Tinelli

   Credits: Example adapted from Dafny tutorial
*/


//      n = 0, 1, 2, 3, 4, 5, 6,  7,  8, ...
// fib(n) = 0, 1, 1, 2, 3, 5, 8, 13, 21, ...
function fib(n: nat): nat
  decreases n;
{
  if n == 0 then 0 
  else if n == 1 then 1 
  else fib(n - 1) + fib(n - 2)
}

// <vc-helpers>
function FibIter(n: nat): nat
  ensures FibIter(n) == fib(n)
  decreases n
{
  if n == 0 then 0
  else if n == 1 then 1
  else FibIter(n-1) + FibIter(n-2)
}
// </vc-helpers>

// <vc-spec>
method ComputeFib(n: nat) returns (f: nat)
  ensures f == fib(n);
// </vc-spec>
// <vc-code>
{
  if n == 0 {
    return 0;
  }
  if n == 1 {
    return 1;
  }

  var a := 0;
  var b := 1;
  var i := 1;

  while i < n
    invariant 0 <= i <= n
    invariant a == fib(i - 1)
    invariant b == fib(i)
    decreases n - i
  {
    var next_fib := a + b;
    a := b;
    b := next_fib;
    i := i + 1;
  }
  return b;
}
// </vc-code>

