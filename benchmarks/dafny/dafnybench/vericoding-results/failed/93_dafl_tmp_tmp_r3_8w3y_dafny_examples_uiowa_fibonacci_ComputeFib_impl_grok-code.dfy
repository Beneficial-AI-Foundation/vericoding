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

// </vc-helpers>

// <vc-spec>
method ComputeFib(n: nat) returns (f: nat)
  ensures f == fib(n);
// </vc-spec>
// <vc-code>
{
  if n == 0 {
    f := 0;
  } else if n == 1 {
    f := 1;
  } else {
    var i := 2;
    var a := 0;
    var b := 1;
    while i <= n
      invariant a == fib(i - 2) && b == fib(i - 1) && 2 <= i <= n + 1
      decreases n - i + 2
    {
      var temp := a + b;
      a := b;
      b := temp;
      i := i + 1;
    }
    f := b;
  }
}
// </vc-code>

