// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): added precondition array bounds check */
function ComputeSum(a: array<int>, N: int): int
    reads a
    requires N >= 0
    requires N <= a.Length
{
    if N == 0 then 0 else a[N-1] + ComputeSum(a, N-1)
}
// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, sum: array<int>, N: int)
    requires N > 0
    requires a.Length == N
    requires sum.Length == 1
    requires N < 1000
    modifies sum
    ensures sum[0] == 6 * N
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): no change, previous code already correct for this part */
{
    var i := 0;
    sum[0] := 0;
    while i < N
        invariant 0 <= i <= N
        invariant sum[0] == 6 * i
    {
        sum[0] := sum[0] + 6;
        i := i + 1;
    }
}
// </vc-code>
