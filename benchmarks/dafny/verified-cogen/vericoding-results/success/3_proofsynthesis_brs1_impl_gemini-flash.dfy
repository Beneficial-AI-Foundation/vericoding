// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added requires clause for N to prevent out-of-bounds access */
function SumArray(a: array<int>, N: int): int
reads a
requires 0 <= N <= a.Length
{
    if N <= 0 then 0 else a[N-1] + SumArray(a, N-1)
}
// </vc-helpers>

// <vc-spec>
method MyFun(a: array<int>, sum: array<int>, N: int)
    requires N > 0
    requires a.Length == N
    requires sum.Length == 1
    modifies a, sum
    ensures sum[0] <= N
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): corrected ensuring sum[0] == N by making loop invariant sum[0] == i */
{
    sum[0] := 0;
    var i := 0;
    while i < N
        invariant 0 <= i <= N
        invariant sum[0] == i
        modifies sum
    {
        sum[0] := sum[0] + 1;
        i := i + 1;
    }
    assert sum[0] == N;
}
// </vc-code>
