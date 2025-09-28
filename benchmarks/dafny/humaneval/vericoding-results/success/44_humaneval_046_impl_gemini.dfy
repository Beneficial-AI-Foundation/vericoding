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
  if n <= 1 {
    result := 0;
  } else if n == 2 {
    result := 2;
  } else if n == 3 {
    result := 0;
  } else {
    var f0 := 0; // fib4_func(0)
    var f1 := 0; // fib4_func(1)
    var f2 := 2; // fib4_func(2)
    var f3 := 0; // fib4_func(3)
    var i := 4;
    while i <= n
      invariant 4 <= i <= n + 1
      invariant f0 == fib4_func(i - 4)
      invariant f1 == fib4_func(i - 3)
      invariant f2 == fib4_func(i - 2)
      invariant f3 == fib4_func(i - 1)
    {
      var current := f0 + f1 + f2 + f3;
      f0 := f1;
      f1 := f2;
      f2 := f3;
      f3 := current;
      i := i + 1;
    }
    result := f3;
  }
}
// </vc-code>
