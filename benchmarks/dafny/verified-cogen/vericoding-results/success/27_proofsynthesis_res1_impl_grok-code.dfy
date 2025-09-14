// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function IntMin(a: int, b: int): int
{
  if a <= b then a else b
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
{
  /* code modified by LLM (iteration 2): cap array elements to at most 1 and sum with loop invariant */
  sum[0] := 0;
  for i := 0 to N - 1
    invariant 0 <= i <= N
    invariant sum[0] <= 2 * i
  {
    a[i] := IntMin(a[i], 1);
    b[i] := IntMin(b[i], 1);
    sum[0] := sum[0] + a[i] + b[i];
  }
}
// </vc-code>
