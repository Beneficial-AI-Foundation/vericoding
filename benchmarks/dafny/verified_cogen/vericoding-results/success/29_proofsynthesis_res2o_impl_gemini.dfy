// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function One(): int { 1 }
// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, b: array<int>, c: array<int>, sum: array<int>, N: int)
	requires N > 0
	requires a.Length == N
	requires b.Length == N
	requires c.Length == N
	requires sum.Length == 1
	requires N < 1000
	ensures sum[0] <= 3 * N
	modifies a, b, c, sum
// </vc-spec>
// <vc-code>
{
    var i: int := 0;
    var total: int := 0;
    while i < N
        invariant 0 <= i <= N
        invariant total == 3 * i
        modifies a, b, c
    {
        a[i] := One();
        b[i] := One();
        c[i] := One();
        total := total + a[i] + b[i] + c[i];
        i := i + 1;
    }
    sum[0] := total;
}
// </vc-code>
