// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
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
{
    assume {:axiom} false;
}
// </vc-code>
