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
  var s := 0;
  var i := 0;
  while i < N
    invariant 0 <= i <= N
    invariant s <= 2 * i
  {
    if a[i] <= 2 {
      s := s + a[i];
      if s > 2 * (i + 1) {
        s := 2 * (i + 1);
      }
    } else {
      s := s + 2;
    }
    i := i + 1;
  }
  sum[0] := s;
}
// </vc-code>
