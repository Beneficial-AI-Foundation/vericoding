// <vc-helpers>
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method CubeSurfaceArea(size: int) returns (area: int)
    requires size > 0
    ensures area == 6 * size * size
// </vc-spec>
// </vc-spec>

// <vc-code>
{
  area := 6 * size * size;
}
// </vc-code>
