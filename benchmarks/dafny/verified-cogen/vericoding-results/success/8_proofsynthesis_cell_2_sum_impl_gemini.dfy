// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function min(x: int, y: int): int { if x < y then x else y }
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
  var i: int := 0;
  while i < N
    invariant 0 <= i <= N
    invariant sum <= 2 * i
  {
    sum := sum + min(a[i], 2);
    i := i + 1;
  }
}
// </vc-code>
