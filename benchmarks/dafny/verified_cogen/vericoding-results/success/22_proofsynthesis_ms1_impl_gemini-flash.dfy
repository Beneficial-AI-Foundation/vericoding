// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): no helpers needed */
// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, sum: array<int>, N: int) 
    requires 
        a.Length == N &&
        sum.Length == 1 &&
        N > 0
    modifies a, sum
    ensures
        sum[0] == 0
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): initialize sum[0] before loop and set a[i] to 0 */
{
    sum[0] := 0;
    var i: int := 0;
    while i < N
        decreases N - i
        modifies a
        invariant 0 <= i <= N
        invariant sum.Length == 1 && sum[0] == 0
        invariant a.Length == N
    {
        a[i] := 0;
        i := i + 1;
    }
}
// </vc-code>
