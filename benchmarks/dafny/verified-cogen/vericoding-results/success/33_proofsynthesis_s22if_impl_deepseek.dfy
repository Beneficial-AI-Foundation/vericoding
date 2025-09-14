// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

lemma helperLemma(n: int)
  requires 0 <= n <= 1000
  ensures n + 2 * n == 3 * n
{
}
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
{
    sum[0] := 0;
    var i := 0;
    while i < N
      invariant 0 <= i <= N
      invariant sum[0] == 3 * i
    {
        sum[0] := sum[0] + 3;
        i := i + 1;
    }
    helperLemma(N);
}
// </vc-code>
