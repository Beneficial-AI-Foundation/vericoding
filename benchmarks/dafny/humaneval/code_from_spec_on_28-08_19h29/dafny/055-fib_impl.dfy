function fib(n: nat): nat
  decreases n
{
  if n == 0 then 0
  else if n == 1 then 1
  else fib(n - 1) + fib(n - 2)
}

// <vc-helpers>
// No additional helpers needed for this implementation
// </vc-helpers>

// <vc-description>
/*
function_signature: def fib(n: int) -> int
Return n-th Fibonacci number.
*/
// </vc-description>

// <vc-spec>
method Fib(n: nat) returns (result: nat)
  ensures result == fib(n)
// </vc-spec>
// <vc-code>
{
  if n == 0 {
    return 0;
  } else if n == 1 {
    return 1;
  } else {
    var a: nat := 0;
    var b: nat := 1;
    var i: nat := 1;
    while i < n
      invariant 0 <= i <= n
      invariant a == fib(i - 1)
      invariant b == fib(i)
    {
      var temp := b;
      b := a + b;
      a := temp;
      i := i + 1;
    }
    return b;
  }
}
// </vc-code>
