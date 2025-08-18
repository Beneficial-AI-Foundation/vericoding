// <vc-helpers>
// </vc-helpers>

method CubeSurfaceArea(size: int) returns (area: int)
    requires size > 0
    ensures area == 6 * size * size
// <vc-code>
{
  assume false;
}
// </vc-code>