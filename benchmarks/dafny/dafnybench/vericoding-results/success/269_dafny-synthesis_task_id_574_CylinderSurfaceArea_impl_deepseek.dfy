

// <vc-helpers>
lemma CylinderSurfaceAreaLemma(r: real, h: real)
  requires r > 0.0 && h > 0.0
  ensures 2.0 * 3.14159265358979323846 * r * (r + h) == 2.0 * 3.14159265358979323846 * (r * r + r * h)
{
  calc {
    2.0 * 3.14159265358979323846 * r * (r + h);
    == { assert r * (r + h) == r * r + r * h; }
    2.0 * 3.14159265358979323846 * (r * r + r * h);
  }
}
// </vc-helpers>

// <vc-spec>
method CylinderSurfaceArea(radius: real, height: real) returns (area: real)
    requires radius > 0.0 && height > 0.0
    ensures area == 2.0 * 3.14159265358979323846 * radius * (radius + height)
// </vc-spec>
// <vc-code>
{
  CylinderSurfaceAreaLemma(radius, height);
  area := 2.0 * 3.14159265358979323846 * (radius * radius + radius * height);
}
// </vc-code>

