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
lemma fib4_unfold(n: int)
  requires n >= 4
  ensures fib4_func(n) == fib4_func(n-1) + fib4_func(n-2) + fib4_func(n-3) + fib4_func(n-4)
{
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
{
  if n == 0 {
    result := 0;
    return;
  }
  if n == 1 {
    result := 0;
    return;
  }
  if n == 2 {
    result := 2;
    return;
  }
  if n == 3 {
    result := 0;
    return;
  }
  var i := 4;
  var v0 := 0;
  var v1 := 0;
  var v2 := 2;
  var v3 := 0;
  while i <= n
    invariant 4 <= i
    invariant i <= n + 1
    invariant v0 == fib4_func(i - 4)
    invariant v1 == fib4_func(i - 3)
    invariant v2 == fib4_func(i - 2)
    invariant v3 == fib4_func(i - 1)
    decreases n - i + 1
  {
    var next := v3 + v2 + v1 + v0;
    assert next == fib4_func(i);
    v0 := v1;
    v1 := v2;
    v2 := v3;
    v3 := next;
    i := i + 1;
  }
  result := v3;
}
// </vc-code>
