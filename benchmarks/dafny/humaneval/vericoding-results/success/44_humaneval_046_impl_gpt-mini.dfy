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
lemma Fib4_nonneg(n: int)
  requires n >= 0
  ensures fib4_func(n) >= 0
  decreases n
{
  if n <= 3 {
    if n == 2 {
      assert fib4_func(2) == 2;
      assert fib4_func(2) >= 0;
    } else {
      assert fib4_func(n) == 0;
    }
  } else {
    Fib4_nonneg(n-1);
    Fib4_nonneg(n-2);
    Fib4_nonneg(n-3);
    Fib4_nonneg(n-4);
    assert fib4_func(n) == fib4_func(n-1) + fib4_func(n-2) + fib4_func(n-3) + fib4_func(n-4);
    assert fib4_func(n) >= 0;
  }
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
  result := fib4_func(n);
}
// </vc-code>
