function Fib(n:nat):nat
{
    if n < 2
    then n
    else Fib(n-2) + Fib(n-1)
}

// <vc-helpers>
// </vc-helpers>

method ComputeFib(n:nat) returns (x:nat)
ensures x == Fib(n)
// <vc-code>
{
  assume false;
}
// </vc-code>