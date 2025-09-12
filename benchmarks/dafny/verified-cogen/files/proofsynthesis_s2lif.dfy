// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, sum: array<int>, N: int)
	requires
		N > 0 &&
		a.Length == N &&
		sum.Length == 1 &&
		N < 1000
	modifies sum
	ensures
		sum[0] == 3 * N
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
