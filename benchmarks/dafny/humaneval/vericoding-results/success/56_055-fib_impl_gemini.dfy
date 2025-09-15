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
  if (n == 0) {
    result := 0;
    return;
  }

  var a: nat := 0;
  var b: nat := 1;
  var i := 1;

  while(i < n)
    invariant 1 <= i <= n
    invariant a == fib(i-1)
    invariant b == fib(i)
  {
    var temp_a := a;
    a := b;
    b := temp_a + b;
    i := i + 1;
  }

  result := b;
}
// </vc-code>
