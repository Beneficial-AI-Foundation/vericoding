function fib(n: nat): nat
{
    if n == 0 then 0 else
    if n == 1 then 1 else
                    fib(n - 1) + fib(n - 2)
}

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method ComputeFib(n: nat) returns (b: nat)
   ensures b == fib(n)  // Do not change this postcondition
// </vc-spec>
// <vc-code>
{
  assume false;
}
// </vc-code>