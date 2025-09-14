// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
lemma NonNegFromPos(n: int) ensures n > 0 ==> 0 <= n { }
// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, sum: array<int>, N: int) 
	requires a.Length == N && sum.Length == 1 && N > 0
	modifies a, sum
	ensures sum[0] <= N
// </vc-spec>
// <vc-code>
{
  sum[0] := 0;
}
// </vc-code>
