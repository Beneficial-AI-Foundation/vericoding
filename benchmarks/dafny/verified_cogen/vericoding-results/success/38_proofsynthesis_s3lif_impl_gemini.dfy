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
  var s := 0;
  var i := 0;
  while i < N
    invariant 0 <= i <= N
    invariant s == 4 * i
  {
    s := s + 4;
    i := i + 1;
  }
  sum[0] := s;
}
// </vc-code>
