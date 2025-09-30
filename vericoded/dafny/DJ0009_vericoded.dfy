// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, N: int) returns (sum: int)
    requires 
        a.Length == N &&
        N <= 0x7FFF_FFFF

    ensures
        sum <= 2*N
// </vc-spec>
// <vc-code>
{
  sum := 0;
  var i := 0;
  while i < N
    invariant 0 <= i <= N
    invariant sum <= 2 * i
  {
    if a[i] <= 2 {
      sum := sum + a[i];
    } else {
      sum := sum + 2;
    }
    i := i + 1;
  }
}
// </vc-code>
