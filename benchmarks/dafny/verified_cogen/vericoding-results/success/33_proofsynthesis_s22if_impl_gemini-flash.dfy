// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): add requires clause to specify valid index */
lemma SumProperty(i: int, a: array<int>) requires 0 <= i < a.Length ensures a[i] + a[i] + a[i] == 3 * a[i] {}
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
/* code modified by LLM (iteration 2): correct loop invariant and ensure final sum */
{
    var total_sum: int := 0;
    var i: int := 0;
    while i < N
        invariant 0 <= i <= N
        invariant total_sum == 3 * i
    {
        total_sum := total_sum + 3;
        i := i + 1;
    }
    sum[0] := total_sum;
}
// </vc-code>
