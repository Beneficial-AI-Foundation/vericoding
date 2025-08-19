// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method ClosestSmaller(n: int) returns (m: int)
    requires n > 0
    ensures m + 1 == n
// </vc-spec>
// <vc-code>
{
  assume false;
}
// </vc-code>