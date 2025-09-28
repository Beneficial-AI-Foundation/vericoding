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
  var count := 0;
  var i := 0;
  while i < N
    invariant 0 <= i <= N && count <= i
  decreases N - i
  {
    if 0 <= a[i] < N { count := count + 1; }
    i := i + 1;
  }
  sum[0] := count;
}
// </vc-code>
