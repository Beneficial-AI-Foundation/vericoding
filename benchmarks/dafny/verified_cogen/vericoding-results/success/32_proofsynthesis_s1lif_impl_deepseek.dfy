// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed unnecessary lemmas */
function double(x: int): int { 2 * x }
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
/* code modified by LLM (iteration 5): Simplified implementation with direct calculation */
{
  sum[0] := 2 * N;
}
// </vc-code>
