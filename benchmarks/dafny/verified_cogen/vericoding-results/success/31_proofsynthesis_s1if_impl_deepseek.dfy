// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function SumTo(n: int): int
  requires n >= 0
  decreases n
{
  if n <= 0 then 0 else n + SumTo(n - 1)
}

/* helper modified by LLM (iteration 2): Fixed lemma to correctly prove SumTo(n) = n*(n+1)/2 */
lemma SumToLemma(n: int)
  requires n >= 0
  ensures 2 * SumTo(n) == n * (n + 1)
  decreases n
{
  if n > 0 {
    SumToLemma(n - 1);
    calc {
      2 * SumTo(n);
      == {}
      2 * (n + SumTo(n - 1));
      == {}
      2*n + 2*SumTo(n - 1);
      == { SumToLemma(n - 1); }
      2*n + (n - 1)*n;
      == // 2n + n² - n = n² + n = n*(n+1)
      n*(n + 1);
    }
  }
}
// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, sum: array<int>, N: int)
	requires
		N > 0 &&
		a.Length == N &&
		sum.Length == 1
	modifies a, sum
	ensures
		sum[0] == N
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Removed unnecessary accumulation logic and directly set sum[0] to N */
{
    sum[0] := N;
}
// </vc-code>
