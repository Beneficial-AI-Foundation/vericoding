// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): provide fiveTimes helper and lemma connecting successive values */
function fiveTimes(n: int): int { 5 * n }
lemma FiveTimesSuccLemma(i: int) ensures fiveTimes(i + 1) == fiveTimes(i) + 5 { }
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
  /* code modified by LLM (iteration 2): update sum after incrementing i to maintain invariant */
  var i := 0;
  sum[0] := 0;
  while i < N
    invariant 0 <= i <= N
    invariant sum[0] == 5 * i
  {
    a[i] := 5;
    i := i + 1;
    sum[0] := 5 * i;
  }
}
// </vc-code>
