method nonZeroReturn(x: int) returns (y: int)
  ensures y != 0
// </vc-spec>
// <vc-code>
{
  y := 1;
}
// </vc-code>