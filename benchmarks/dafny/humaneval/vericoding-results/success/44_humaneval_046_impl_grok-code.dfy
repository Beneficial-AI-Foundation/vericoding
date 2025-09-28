// <vc-preamble>

function fib4_func(n: int): int
    requires n >= 0
{
    if n == 0 then 0
    else if n == 1 then 0
    else if n == 2 then 2
    else if n == 3 then 0
    else fib4_func(n-1) + fib4_func(n-2) + fib4_func(n-3) + fib4_func(n-4)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method fib4(n: int) returns (result: int)
    requires n >= 0
    ensures result == fib4_func(n)
    ensures n == 0 ==> result == 0
    ensures n == 1 ==> result == 0
    ensures n == 2 ==> result == 2
    ensures n == 3 ==> result == 0
    ensures n >= 4 ==> result == fib4_func(n-1) + fib4_func(n-2) + fib4_func(n-3) + fib4_func(n-4)
// </vc-spec>
// <vc-code>
{
  if n == 0 {
    return 0;
  }
  else if n == 1 {
    return 0;
  }
  else if n == 2 {
    return 2;
  }
  else if n == 3 {
    return 0;
  }
  else {
    var a, b, c, d, i := 0, 0, 2, 0, 4;
    while i <= n
      invariant 4 <= i <= n + 1
      invariant a == fib4_func(i - 4)
      invariant b == fib4_func(i - 3)
      invariant c == fib4_func(i - 2)
      invariant d == fib4_func(i - 1)
    {
      var next := a + b + c + d;
      a := b;
      b := c;
      c := d;
      d := next;
      i := i + 1;
    }
    return d;
  }
}
// </vc-code>
