// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): add reads clause */
function S(a: array<int>, i: int, k: int): int
  reads a
  requires 0 <= i
  requires i + k <= a.Length
  requires k >= 0
  ensures S(a, i, k) == (if k == 0 then 0 else a[i] + S(a, i + 1, k - 1))
  decreases k
{
  if k == 0 then 0 else a[i] + S(a, i + 1, k - 1)
}
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
/* code modified by LLM (iteration 3): no change needed, fix was in helper */
{
  var i: int := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> a[j] == 4
  {
    a[i] := 4;
    i := i + 1;
  }
  sum[0] := 4 * N;
}
// </vc-code>
