// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, sum: array<int>, N: int)
    requires a.Length == N
    requires sum.Length == 1
    requires N > 0
    requires N < 1000
    modifies sum
    ensures sum[0] <= 3 * N
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Fixed assignment operator from = to := to resolve compilation error */
  sum[0] := 3 * N;
}
// </vc-code>
