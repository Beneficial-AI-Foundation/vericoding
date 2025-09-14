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
    return 0;
  } else if n == 1 {
    return 1;
  } else {
    var i := 2;
    var a := 0;
    var b := 1;
    while i <= n
      invariant 2 <= i <= n+1
      invariant a == fib(i-2)
      invariant b == fib(i-1)
    {
      a, b := b, a + b;
      i := i + 1;
    }
    return b;
  }
}
// </vc-code>

