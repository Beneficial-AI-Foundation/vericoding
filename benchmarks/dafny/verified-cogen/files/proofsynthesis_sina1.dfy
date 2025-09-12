// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, sum: array<int>, N: int)
	requires
		N > 0 &&
		a.Length == N &&
		sum.Length == 1
	modifies a, sum
	ensures
		forall k:int :: 0 <= k < N ==> a[k] == N
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
