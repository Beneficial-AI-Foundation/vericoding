// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added reads clause to sum_elements */
function sum_elements(a: array<int>, b: array<int>, limit: int): int
    reads a, b
    requires 0 <= limit <= a.Length
    requires a.Length == b.Length
{
    if limit == 0 then 0
    else sum_elements(a, b, limit - 1) + a[limit - 1] + b[limit - 1]
}
// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, b: array<int>, sum: array<int>, N: int)
	requires N > 0
	requires a.Length == N
	requires b.Length == N
	requires sum.Length == 1
	requires N < 1000
	ensures sum[0] <= 2 * N
	modifies a, b, sum
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): strengthened loop invariant for sum calculation */
{
    var i := 0;
    while i < N
        invariant 0 <= i <= N
        invariant forall k :: 0 <= k < i ==> a[k] <= 1 && b[k] <= 1 && a[k] + b[k] <= 2
        decreases N - i
    {
        a[i] := i % 2;
        b[i] := i % 2;
        i := i + 1;
    }

    var current_sum := 0;
    i := 0;
    while i < N
        invariant 0 <= i <= N
        invariant current_sum == sum_elements(a, b, i)
        invariant current_sum <= 2 * i
        decreases N - i
    {
        current_sum := current_sum + a[i] + b[i];
        i := i + 1;
    }
    sum[0] := current_sum;
}
// </vc-code>
