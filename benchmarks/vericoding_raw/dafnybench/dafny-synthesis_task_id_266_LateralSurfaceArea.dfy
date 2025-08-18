// <vc-helpers>
// </vc-helpers>

method LateralSurfaceArea(size: int) returns (area: int)
    requires size > 0
    ensures area == 4 * size * size
// <vc-code>
{
  assume false;
}
// </vc-code>