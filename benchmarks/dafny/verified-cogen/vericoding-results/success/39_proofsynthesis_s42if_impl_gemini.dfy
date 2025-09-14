// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, sum: array<int>, N: int)
	requires N > 0
	requires a.Length == N
	requires sum.Length == 1
	requires N < 1000
	ensures sum[0] == 5 * N
	modifies a, sum
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): reordered statements to handle potential aliasing */
    sum[0] := 0;
    var i := 0;
    while i < N
        invariant 0 <= i <= N
        invariant sum[0] == 5 * i
        invariant forall k :: 0 <= k < i ==> a[k] == 5
        modifies a, sum
    {
        sum[0] := sum[0] + 5;
        a[i] := 5;
        i := i + 1;
    }
}
// </vc-code>
