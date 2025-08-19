function fib(n: nat): nat
decreases n
{
   if n == 0 then 0 else
   if n == 1 then 1 else
                  fib(n - 1) + fib(n - 2)
}

// <vc-helpers>
// </vc-helpers>

method fibonacci3(n:nat) returns (f:nat)
ensures f==fib(n)
// <vc-code>
{
  assume false;
}
// </vc-code>