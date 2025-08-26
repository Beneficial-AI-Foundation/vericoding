function fib(n: nat): nat
{
    if n == 0 then 0 else
    if n == 1 then 1 else
                    fib(n - 1) + fib(n - 2)
}

// <vc-helpers>
// </vc-helpers>

method ComputeFib(n: nat) returns (b: nat)
   ensures b == fib(n)  // Do not change this postcondition
// </vc-spec>
// <vc-code>
{
  if n == 0 {
    b := 0;
  } else if n == 1 {
    b := 1;
  } else {
    var prev2 := 0;
    var prev1 := 1;
    var i := 2;
    
    while i <= n
      invariant 2 <= i <= n + 1
      invariant prev2 == fib(i - 2)
      invariant prev1 == fib(i - 1)
    {
      var curr := prev1 + prev2;
      prev2 := prev1;
      prev1 := curr;
      i := i + 1;
    }
    
    b := prev1;
  }
}
// </vc-code>