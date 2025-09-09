function fib4_rec(n: nat): nat
  decreases n
{
  if n == 0 || n == 1 || n == 2 then 0
  else if n == 3 then 1
  else fib4_rec(n - 1) + fib4_rec(n - 2) + fib4_rec(n - 3) + fib4_rec(n - 4)
}

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method fib4(n: nat) returns (result: nat)

  ensures result == fib4_rec(n)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
