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
lemma FibMonotonic(i: nat, j: nat)
  requires i <= j
  ensures fib(i) <= fib(j)
  decreases j - i
{
  if i == j {
    // Base case: fib(i) == fib(j)
  } else if i == 0 {
    // fib(0) = 0, and fib(j) >= 0 for all j
  } else if i == 1 {
    if j == 1 {
      // fib(1) == fib(1)
    } else {
      // j >= 2, so fib(j) = fib(j-1) + fib(j-2) >= fib(j-2) >= fib(1)
      FibMonotonic(1, j-1);
    }
  } else {
    // i >= 2, j >= i >= 2
    FibMonotonic(i, j-1);
    if j >= 2 && i <= j-2 {
      FibMonotonic(i, j-2);
    }
  }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method ComputeFib(n: nat) returns (f: nat)
  ensures f == fib(n);
// </vc-spec>
// </vc-spec>

// <vc-code>
{
  if n == 0 {
    f := 0;
  } else if n == 1 {
    f := 1;
  } else {
    var prev2 := 0;
    var prev1 := 1;
    var i := 2;
    
    while i <= n
      invariant 2 <= i <= n + 1
      invariant prev2 == fib(i - 2)
      invariant prev1 == fib(i - 1)
      decreases n - i
    {
      var current := prev1 + prev2;
      prev2 := prev1;
      prev1 := current;
      i := i + 1;
    }
    
    f := prev1;
  }
}
// </vc-code>
