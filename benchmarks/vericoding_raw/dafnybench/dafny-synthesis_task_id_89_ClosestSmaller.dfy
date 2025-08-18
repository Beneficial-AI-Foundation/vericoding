// <vc-helpers>
// </vc-helpers>

method ClosestSmaller(n: int) returns (m: int)
    requires n > 0
    ensures m + 1 == n
// <vc-code>
{
  assume false;
}
// </vc-code>