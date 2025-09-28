// <vc-preamble>

predicate ValidInput(n: int) {
    n > 0
}

function fib_spec(n: int): int
    requires n > 0
{
    if n == 1 then 1
    else if n == 2 then 1
    else fib_spec(n-1) + fib_spec(n-2)
}
// </vc-preamble>

// <vc-helpers>
lemma fib_spec_recurrence(k: int)
  requires k > 2
  ensures fib_spec(k) == fib_spec(k - 1) + fib_spec(k - 2)
{
}

// </vc-helpers>

// <vc-spec>
method fib(n: int) returns (result: int)
    requires ValidInput(n)
    ensures result == fib_spec(n)
    ensures result > 0
// </vc-spec>
// <vc-code>
{
  if n == 1 || n == 2 {
    result := 1;
  } else {
    var i := 2;
    var a := 1;
    var b := 1;
    while i < n
      invariant n > 0
      invariant i >= 2
      invariant i <= n
      invariant a == fib_spec(i - 1)
      invariant b == fib_spec(i)
      invariant a > 0 && b > 0
      decreases n - i
    {
      fib_spec_recurrence(i + 1);
      a, b := b, a + b;
      i := i + 1;
    }
    result := b;
  }
}
// </vc-code>
