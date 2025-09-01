function fib(n: nat): nat
  decreases n
{
  if n == 0 then 0
  else if n == 1 then 1
  else fib(n - 1) + fib(n - 2)
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ComputeFib(n: nat) returns (result: nat)
  // post-conditions-start
  ensures result == fib(n)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var a := 0;
  var b := 1;
  var i := 0;
  while (i < n)
    invariant 0 <= i <= n
    invariant a == fib(i)
    invariant b == fib(i + 1)
  {
    a, b := b, a + b;
    i := i + 1;
  }
  result := a;
}
// </vc-code>

