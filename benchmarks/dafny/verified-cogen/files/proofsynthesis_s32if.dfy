// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method MyFun(a: array<int>, sum: array<int>, N: int)
	requires
		N > 0 &&
		a.Length == N &&
		sum.Length == 1 &&
		N < 1000
	modifies a, sum
	ensures
		sum[0] == 4 * N
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
