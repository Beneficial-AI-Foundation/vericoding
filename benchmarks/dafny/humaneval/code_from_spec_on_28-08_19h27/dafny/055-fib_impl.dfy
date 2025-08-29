function fib(n: nat): nat
  decreases n
{
  if n == 0 then 0
  else if n == 1 then 1
  else fib(n - 1) + fib(n - 2)
}

// <vc-helpers>
// </vc-helpers>

// <vc-description>
/*
function_signature: def fib(n: int) -> int
Return n-th Fibonacci number.
*/
// </vc-description>

// <vc-spec>
method fib_method(n: nat) returns (result: nat)
  ensures result == fib(n)
// </vc-spec>
// <vc-code>
{
  result := fib(n);
}
// </vc-code>
