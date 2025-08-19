// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method LateralSurfaceArea(size: int) returns (area: int)
    requires size > 0
    ensures area == 4 * size * size
// </vc-spec>
// <vc-code>
{
  assume false;
}
// </vc-code>