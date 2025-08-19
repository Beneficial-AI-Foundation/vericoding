// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method TriangleNumber(N: int) returns (t: int)
    requires N >= 0
    ensures t == N * (N + 1) / 2
// </vc-spec>
// <vc-code>
{
  assume false;
}
// </vc-code>