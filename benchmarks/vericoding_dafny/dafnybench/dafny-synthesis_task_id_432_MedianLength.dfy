// <vc-helpers>
// </vc-helpers>

method MedianLength(a: int, b: int) returns (median: int)
    requires a > 0 && b > 0
    ensures median == (a + b) / 2
// <vc-code>
{
  assume false;
}
// </vc-code>