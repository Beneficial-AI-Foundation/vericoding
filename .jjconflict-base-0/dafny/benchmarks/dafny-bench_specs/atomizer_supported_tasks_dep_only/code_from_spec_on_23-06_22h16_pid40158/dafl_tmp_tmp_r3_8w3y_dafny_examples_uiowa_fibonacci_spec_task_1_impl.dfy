/*
   CS:5810 Formal Methods in Software Engineering
   Fall 2017
   The University of Iowa
   
   Instructor: Cesare Tinelli

   Credits: Example adapted from Dafny tutorial
*/


//      n = 0, 1, 2, 3, 4, 5, 6,  7,  8, ...
// fib(n) = 0, 1, 1, 2, 3, 5, 8, 13, 21, ...
// ATOM 
   



//      n = 0, 1, 2, 3, 4, 5, 6,  7,  8, ...
// fib(n) = 0, 1, 1, 2, 3, 5, 8, 13, 21, ...
function fib(n: nat): nat
{
  if n == 0 then 0 
  else if n == 1 then 1 
  else fib(n - 1) + fib(n - 2)
}


// IMPL ComputeFib

method ComputeFib(n: nat) returns (f: nat)
  ensures f == fib(n);
{
  if n == 0 {
    f := 0;
  } else if n == 1 {
    f := 1;
  } else {
    var prev := 0;
    var curr := 1;
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
    
    f := curr;
  }
}