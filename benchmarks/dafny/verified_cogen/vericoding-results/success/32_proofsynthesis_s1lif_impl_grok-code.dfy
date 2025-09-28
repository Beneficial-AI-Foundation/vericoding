// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, sum: array<int>, N: int)
    requires N > 0
    requires a.Length == N
    requires sum.Length == 1
    requires N < 1000
    modifies a, sum
    ensures sum[0] == 2 * N
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): set sum[0] to 2 * N to satisfy the ensures clause */
  sum[0] := 2 * N;
}
// </vc-code>
