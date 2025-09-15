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
    result := 0;
  } else if n == 1 {
    result := 1;
  } else {
    var a := 0;
    var b := 1;
    var i := 2;
    while i <= n
      invariant 2 <= i <= n + 1
      invariant a == fib(i - 2)
      invariant b == fib(i - 1)
    {
      var temp := a + b;
      a := b;
      b := temp;
      i := i + 1;
    }
    result := b;
  }
}
// </vc-code>
