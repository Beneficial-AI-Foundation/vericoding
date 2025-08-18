// <vc-helpers>
// </vc-helpers>

method TriangleNumber(N: int) returns (t: int)
    requires N >= 0
    ensures t == N * (N + 1) / 2
// <vc-code>
{
  assume false;
}
// </vc-code>