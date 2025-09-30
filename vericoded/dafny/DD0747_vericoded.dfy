

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method CylinderSurfaceArea(radius: real, height: real) returns (area: real)
    requires radius > 0.0 && height > 0.0
    ensures area == 2.0 * 3.14159265358979323846 * radius * (radius + height)
// </vc-spec>
// <vc-code>
{
    area := 2.0 * 3.14159265358979323846 * radius * (radius + height);
}
// </vc-code>

