// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, sum: array<int>, N: int)
    requires N > 0
    requires a.Length == N
    requires sum.Length == 1
    requires N < 1000
    modifies sum
    ensures sum[0] == 6 * N
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): fixed loop invariant initialization */
  sum[0] := 0;
  var i := 0;
  while i < N
    invariant 0 <= i <= N
    invariant sum[0] == 6 * i
  {
    sum[0] := sum[0] + 6;
    i := i + 1;
  }
}
// </vc-code>
