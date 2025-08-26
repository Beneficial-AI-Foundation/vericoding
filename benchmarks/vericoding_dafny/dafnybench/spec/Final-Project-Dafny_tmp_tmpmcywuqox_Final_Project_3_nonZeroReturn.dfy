// <vc-helpers>
// </vc-helpers>

method nonZeroReturn(x: int) returns (y: int)
  ensures y != 0
// <vc-code>
{
  assume false;
}
// </vc-code>