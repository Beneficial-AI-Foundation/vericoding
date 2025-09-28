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
    ensures
        sum[0] <= 2 * N
    modifies a, sum
// </vc-spec>
// <vc-code>
{
  for i := 0 to N-1 {
    a[i] := 2;
  }
  sum[0] := 2 * N;
}
// </vc-code>
