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
    ensures sum[0] == 4 * N
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var temp_sum := 0;
  while i < N
    invariant 0 <= i <= N
    invariant temp_sum == 4 * i
  {
    temp_sum := temp_sum + 4;
    i := i + 1;
  }
  sum[0] := temp_sum;
}
// </vc-code>
