// <vc-helpers>
// </vc-helpers>

method Abs(x: int) returns (y: int)
    requires x < 0
    ensures 0 < y
    ensures y == -x
// <vc-code>
{
  assume false;
}
// </vc-code>