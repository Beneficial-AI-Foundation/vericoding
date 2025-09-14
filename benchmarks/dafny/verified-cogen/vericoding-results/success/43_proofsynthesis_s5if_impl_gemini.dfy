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
    ensures sum[0] == 5 * N
    modifies a, sum
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var total := 0;
  while i < N
    invariant 0 <= i <= N
    invariant total == 5 * i
  {
    a[i] := 5;
    total := total + 5;
    i := i + 1;
  }
  sum[0] := total;
}
// </vc-code>
