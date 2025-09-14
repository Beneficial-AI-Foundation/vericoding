// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function One(): int { 1 }
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
{
    var s: int := 0;
    var i: int := 0;
    while (i < N)
        invariant 0 <= i <= N
        invariant s == 2 * i
        modifies a, b
    {
        a[i] := One();
        b[i] := One();
        s := s + a[i] + b[i];
        i := i + 1;
    }
    sum[0] := s;
}
// </vc-code>
