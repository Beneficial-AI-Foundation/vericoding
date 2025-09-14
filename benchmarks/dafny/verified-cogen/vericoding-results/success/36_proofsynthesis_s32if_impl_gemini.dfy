// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function FourTimes(x: int): int { 4 * x }
// </vc-helpers>

// <vc-spec>
method MyFun(a: array<int>, sum: array<int>, N: int)
	requires
		N > 0 &&
		a.Length == N &&
		sum.Length == 1 &&
		N < 1000
	modifies a, sum
	ensures
		sum[0] == 4 * N
// </vc-spec>
// <vc-code>
{
    sum[0] := 0;
    var i := 0;
    while i < N
        invariant 0 <= i <= N
        invariant sum[0] == FourTimes(i)
        modifies a, sum
    {
        a[i] := 0;
        sum[0] := sum[0] + 4;
        i := i + 1;
    }
}
// </vc-code>
