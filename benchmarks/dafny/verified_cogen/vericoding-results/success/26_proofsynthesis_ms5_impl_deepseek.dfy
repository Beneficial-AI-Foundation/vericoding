// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, sum: array<int>, N: int) 
    requires 
        a.Length == N &&
        sum.Length == 1 &&
        N > 0 &&
        N < 1000
    modifies sum
    ensures
        sum[0] <= 4 * N
// </vc-spec>
// <vc-code>
{
  var i := 0;
  sum[0] := 0;
  while (i < N)
    invariant i <= N
    invariant sum[0] == 4 * i
    decreases N - i
  {
    sum[0] := sum[0] + 4;
    i := i + 1;
  }
}
// </vc-code>
