// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): helper function is not required here */
// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, sum: array<int>, N: int)
    requires N > 0
    requires a.Length == N
    requires sum.Length == 1
    requires N < 1000
    modifies sum
    ensures sum[0] == 4 * N
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): initialize sum[0] to 0 before the loop */
{
    sum[0] := 0;
    var k := 0;
    while k < N
        invariant 0 <= k <= N
        invariant sum[0] == 4 * k
    {
        sum[0] := sum[0] + 4;
        k := k + 1;
    }
}
// </vc-code>
