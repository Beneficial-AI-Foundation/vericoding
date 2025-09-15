// <vc-preamble>
function fib(n: nat): nat
  decreases n
{
  if n == 0 then 0
  else if n == 1 then 1
  else fib(n - 1) + fib(n - 2)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ComputeFib(n: nat) returns (result: nat)

  ensures result == fib(n)
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
      invariant i <= n + 1
      invariant a == fib(i - 2)
      invariant b == fib(i - 1)
      decreases n - i
    {
      var c := a + b;
      a := b;
      b := c;
      i := i + 1;
    }
    return b;
  }
}
// </vc-code>
