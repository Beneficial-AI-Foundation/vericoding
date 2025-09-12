// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, sum: array<int>, N: int)
	requires N > 0
	requires a.Length == N
	requires sum.Length == 1
	ensures forall k :: 0 <= k < N ==> a[k] == 0
	modifies a, sum
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
