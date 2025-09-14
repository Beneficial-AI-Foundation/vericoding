// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added minHelper for comparison */
function minHelper(a: int, b: int): int { if a < b then a else b }
// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, sum: array<int>, N: int)
    requires a.Length == N
    requires sum.Length == 1
    requires N > 0
    requires N < 1000
    modifies sum
    ensures sum[0] <= 3 * N
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): fixed loop invariant violations */
  var total := 0;
  var i := 0;
  while i < N
    invariant 0 <= i <= N
    invariant total <= 3 * i
  {
    total := total + minHelper(a[i], 3);
    i := i + 1;
  }
  sum[0] := total;
}
// </vc-code>
