function fib(n: nat): nat
decreases n
{
   if n == 0 then 0 else
   if n == 1 then 1 else
                  fib(n - 1) + fib(n - 2)
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method fibonacci1(n:nat) returns (f:nat)
ensures f==fib(n)
// </vc-spec>
// <vc-code>
{
  if n == 0 {
    f := 0;
  } else if n == 1 {
    f := 1;
  } else {
    var i := 2;
    var prev1 := 1;
    var prev2 := 0;
    f := prev1 + prev2;
    
    while i < n
      invariant 2 <= i <= n
      invariant prev1 == fib(i - 1)
      invariant prev2 == fib(i - 2)
      invariant f == fib(i)
    {
      prev2 := prev1;
      prev1 := f;
      f := prev1 + prev2;
      i := i + 1;
    }
  }
}
// </vc-code>

