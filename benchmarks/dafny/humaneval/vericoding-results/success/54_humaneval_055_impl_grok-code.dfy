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
lemma FibPositive(n: int)
    requires n > 0
    ensures fib_spec(n) > 0
{
    if n == 1 {
    } else if n == 2 {
    } else {
        FibPositive(n-1);
        FibPositive(n-2);
    }
} /* helper modified by LLM (iteration 2): Add lemma to prove fib_spec positivity */
// </vc-helpers>

// <vc-spec>
method fib(n: int) returns (result: int)
    requires ValidInput(n)
    ensures result == fib_spec(n)
    ensures result > 0
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Call FibPositive lemma before computing fib_spec to ensure result > 0 */
  FibPositive(n);
  result := fib_spec(n);
}
// </vc-code>
