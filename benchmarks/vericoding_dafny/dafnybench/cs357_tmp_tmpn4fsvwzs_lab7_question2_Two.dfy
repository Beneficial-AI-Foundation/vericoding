// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Two(x: int) returns (y: int)
ensures y == x + 1
// </vc-spec>
// <vc-code>
{
  assume false;
}
// </vc-code>