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
/* helper modified by LLM (iteration 2): Removed 'this' from reads clause. */
function ComputeFib4(k: int, n_param: int): int
    requires 0 <= k <= n_param
    decreases k
{
    if k == 0 then 0
    else if k == 1 then 0
    else if k == 2 then 2
    else if k == 3 then 0
    else ComputeFib4(k-1, n_param) + ComputeFib4(k-2, n_param) + ComputeFib4(k-3, n_param) + ComputeFib4(k-4, n_param)
}
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
/* code modified by LLM (iteration 2): Implemented Fibonacci sequence with iterative approach. */
{
  if n == 0 {
    result := 0;
  } else if n == 1 {
    result := 0;
  } else if n == 2 {
    result := 2;
  } else if n == 3 {
    result := 0;
  } else {
    var i: int := 4;
    var f0: int := 0;
    var f1: int := 0;
    var f2: int := 2;
    var f3: int := 0;
    while i <= n
      invariant 4 <= i <= n + 1
      invariant f0 == fib4_func(i-4)
      invariant f1 == fib4_func(i-3)
      invariant f2 == fib4_func(i-2)
      invariant f3 == fib4_func(i-1)
      decreases n - i
    {
      var next_f: int := f0 + f1 + f2 + f3;
      f0 := f1;
      f1 := f2;
      f2 := f3;
      f3 := next_f;
      i := i + 1;
    }
    result := f3;
  }
}
// </vc-code>
