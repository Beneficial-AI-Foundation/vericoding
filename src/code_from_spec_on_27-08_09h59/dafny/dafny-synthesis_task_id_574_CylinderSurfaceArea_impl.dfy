// <vc-helpers>
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method CylinderSurfaceArea(radius: real, height: real) returns (area: real)
    requires radius > 0.0 && height > 0.0
    ensures area == 2.0 * 3.14159265358979323846 * radius * (radius + height)
// </vc-spec>
// </vc-spec>

// <vc-code>
{
  var pi := 3.14159265358979323846;
  area := 2.0 * pi * radius * (radius + height);
}
// </vc-code>
