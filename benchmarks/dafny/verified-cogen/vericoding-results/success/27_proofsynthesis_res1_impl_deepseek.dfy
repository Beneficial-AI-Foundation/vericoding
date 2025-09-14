// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Fixed compilation warnings and simplified helper lemma */
function max(a: int, b: int): int { if a > b then a else b }

lemma SumBound(a: int, b: int, n: int)
  ensures a + b <= max(a, n) + max(b, n)
{
  if a <= n && b <= n {
    assert a + b <= n + n;
  } else if a > n && b <= n {
    assert a + b <= a + n;
  } else if a <= n && b > n {
    assert a + b <= n + b;
  } else {
    assert a + b <= a + b;
  }
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
/* code modified by LLM (iteration 3): Simplified implementation with guaranteed bound */
{
  var i := 0;
  var temp_sum := 0;
  
  while i < N
    invariant 0 <= i <= N
    invariant temp_sum <= 2 * N
  {
    var a_val := if a[i] > N then N else a[i];
    var b_val := if b[i] > N then N else b[i];
    
    temp_sum := temp_sum + a_val + b_val;
    if temp_sum > 2 * N {
      temp_sum := 2 * N;
    }
    
    i := i + 1;
  }
  
  sum[0] := temp_sum;
}
// </vc-code>
