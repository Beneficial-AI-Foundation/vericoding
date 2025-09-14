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
lemma FibIterativeCorrectness(n: nat, a: nat, b: nat, i: nat)
  requires i <= n
  requires a == fib(i)
  requires b == fib(i + 1)
  ensures var (final_a, final_b) := FibIterative(n - i, a, b); final_a == fib(n)
  decreases n - i
{
  if i < n {
    FibIterativeCorrectness(n, b, a + b, i + 1);
  }
}

function FibIterative(steps: nat, a: nat, b: nat): (nat, nat)
  decreases steps
{
  if steps == 0 then (a, b)
  else FibIterative(steps - 1, b, a + b)
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
  } else if n == 1 {
    return 1;
  } else {
    var a := 0;
    var b := 1;
    var i := 1;
    
    while i < n
      invariant 1 <= i <= n
      invariant a == fib(i - 1)
      invariant b == fib(i)
      decreases n - i
    {
      var temp := a + b;
      a := b;
      b := temp;
      i := i + 1;
    }
    
    return b;
  }
}
// </vc-code>

