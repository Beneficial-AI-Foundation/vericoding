// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): simple arithmetic helper to compute x + 2 */
function add2(x: int): int { x + 2 }
// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, b: array<int>, sum: array<int>, N: int)
	requires N > 0
	requires a.Length == N
	requires b.Length == N
	requires sum.Length == 1
	requires N < 1000
	ensures forall k :: 0 <= k < N ==> b[k] == N + 2
	modifies a, b, sum
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): fill b with N+2; set sum[0] consistently even if it aliases b */
  var i := 0;
  while i < N
    invariant 0 <= i <= N
    invariant forall k :: 0 <= k < i ==> b[k] == N + 2
    decreases N - i
  {
    b[i] := add2(N);
    i := i + 1;
  }
  sum[0] := add2(N);
}
// </vc-code>
