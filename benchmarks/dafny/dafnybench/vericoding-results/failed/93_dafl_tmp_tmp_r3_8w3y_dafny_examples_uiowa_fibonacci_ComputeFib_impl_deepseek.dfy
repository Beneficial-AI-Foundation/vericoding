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
lemma FibLemma(n: nat)
  ensures fib(n+2) == fib(n+1) + fib(n)
  decreases n
{
  if n > 0 {
    FibLemma(n-1);
  } else {
    // Base case: n == 0
    // fib(2) == fib(1) + fib(0) => 1 == 1 + 0
  }
}

lemma FibMonotonic(n: nat)
  ensures fib(n) <= fib(n+1)
  decreases n
{
  if n == 0 {
  } else if n == 1 {
  } else {
    FibMonotonic(n-1);
    FibMonotonic(n-2);
  }
}
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
    var a := 0;
    var b := 1;
    var i := 1;
    while i < n
      invariant i <= n
      invariant a == fib(i-1)
      invariant b == fib(i)
      decreases n - i
    {
      var next := a + b;
      a := b;
      b := next;
      i := i + 1;
      
      // Update the lemma call to use the current state
      if i - 2 >= 0 {
        FibLemma(i-2);
      }
    }
    f := b;
  }
}
// </vc-code>

