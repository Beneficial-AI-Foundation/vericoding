

// <vc-helpers>
lemma MultiplyAssociative(x: real, y: real, z: real)
    ensures x * y * z == x * (y * z)
{
}
// </vc-helpers>

// <vc-spec>
method CylinderLateralSurfaceArea(radius: real, height: real) returns (area: real)
    requires radius > 0.0 && height > 0.0
    ensures area == 2.0 * (radius * height) * 3.14
// </vc-spec>
// <vc-code>
{
  area := 2.0 * radius * height * 3.14;
  MultiplyAssociative(2.0, radius, height);
}
// </vc-code>

