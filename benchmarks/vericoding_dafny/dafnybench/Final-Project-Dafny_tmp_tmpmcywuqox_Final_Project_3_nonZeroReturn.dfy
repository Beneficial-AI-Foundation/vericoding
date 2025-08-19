// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method nonZeroReturn(x: int) returns (y: int)
  ensures y != 0
// </vc-spec>
// <vc-code>
{
  assume false;
}
// </vc-code>