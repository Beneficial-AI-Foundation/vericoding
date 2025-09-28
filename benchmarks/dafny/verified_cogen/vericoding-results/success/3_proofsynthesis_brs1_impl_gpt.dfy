// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
lemma ZeroLeFromPos(N: int) requires N > 0 ensures 0 <= N { }
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
  sum[0] := 0;
}
// </vc-code>
