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
// No additional helpers needed for this implementation
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
    var prev := 1;  // fib(1)
    var curr := 1;  // fib(2)
    
    while i < n
      invariant 2 <= i <= n
      invariant prev == fib(i - 1)
      invariant curr == fib(i)
    {
      var temp := curr;
      curr := prev + curr;
      prev := temp;
      i := i + 1;
    }
    
    f := curr;
  }
}
// </vc-code>

