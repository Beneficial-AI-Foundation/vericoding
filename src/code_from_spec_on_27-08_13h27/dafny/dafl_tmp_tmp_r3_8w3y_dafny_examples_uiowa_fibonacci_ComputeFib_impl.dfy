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
lemma FibMonotonic(n: nat, m: nat)
  requires n <= m
  ensures fib(n) <= fib(m)
  decreases m
{
  if n == m {
    // Base case: n == m, so fib(n) == fib(m)
  } else if n == 0 {
    // Base case: n == 0, fib(0) = 0, which is less than or equal to any fib(m)
  } else if n == 1 {
    if m == 1 {
    } else {
      assert fib(1) == 1;
      assert fib(m) >= 1;
    }
  } else {
    FibMonotonic(n - 1, m - 1);
    FibMonotonic(n - 2, m - 2);
    assert fib(n) == fib(n - 1) + fib(n - 2);
    assert fib(m) == fib(m - 1) + fib(m - 2);
    assert fib(n - 1) <= fib(m - 1);
    assert fib(n - 2) <= fib(m - 2);
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
method ComputeFibImpl(n: nat) returns (f: nat)
  ensures f == fib(n)
{
  if n == 0 {
    return 0;
  } else if n == 1 {
    return 1;
  }
  
  var f0 := 0;
  var f1 := 1;
  var i := 1;
  while i < n
    invariant 0 <= i <= n
    invariant f0 == fib(i - 1)
    invariant f1 == fib(i)
  {
    var f2 := f0 + f1;
    f0 := f1;
    f1 := f2;
    i := i + 1;
  }
  return f1;
}
// </vc-code>
