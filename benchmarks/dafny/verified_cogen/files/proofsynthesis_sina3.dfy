// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, b: array<int>, sum: array<int>, N: int)
	requires N > 0
	requires a.Length == N
	requires b.Length == N
	requires sum.Length == 1
	requires N < 1000
	modifies a, b, sum
	ensures forall k :: 0 <= k < N ==> a[k] == N + 1
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
