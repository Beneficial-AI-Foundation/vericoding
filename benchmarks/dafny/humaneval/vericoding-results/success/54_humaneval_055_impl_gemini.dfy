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
lemma lemma_fib_spec_positive(n: int)
    requires n > 0
    ensures fib_spec(n) > 0
{
    if n > 2 {
        lemma_fib_spec_positive(n-1);
        lemma_fib_spec_positive(n-2);
    }
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
  if n <= 2 {
    result := 1;
  } else {
    var i := 2;
    var a := 1; 
    var b := 1;

    while i < n
      invariant 2 <= i <= n
      invariant a == fib_spec(i - 1)
      invariant b == fib_spec(i)
      decreases n - i
    {
      a, b := b, a + b;
      i := i + 1;
    }
    result := b;
  }
}
// </vc-code>
