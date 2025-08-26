method Two(x: int) returns (y: int)
ensures y == x + 1
// </vc-spec>
// <vc-code>
{
  y := x + 1;
}
// </vc-code>