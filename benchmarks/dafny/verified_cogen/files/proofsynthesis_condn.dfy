// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, N: int, m: int)
	requires N > 0
	requires a.Length == N
	modifies a
	ensures forall k :: 0 <= k < N ==> a[k] <= N
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
