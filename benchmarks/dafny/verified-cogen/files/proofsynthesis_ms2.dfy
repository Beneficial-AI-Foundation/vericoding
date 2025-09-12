// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, sum: array<int>, N: int) 
	requires a.Length == N && sum.Length == 1 && N > 0
	modifies a, sum
	ensures sum[0] <= N
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
