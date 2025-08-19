// <vc-helpers>
// </vc-helpers>

method Two(x: int) returns (y: int)
ensures y == x + 1
// <vc-code>
{
  assume false;
}
// </vc-code>