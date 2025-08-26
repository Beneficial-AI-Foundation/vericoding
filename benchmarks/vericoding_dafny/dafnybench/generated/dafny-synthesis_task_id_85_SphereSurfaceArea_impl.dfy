// The specification requires:
// - Input: `radius > 0.0`
// - Output: `area == 4.0 * 3.14159265358979323846 * radius * radius`
//
// This is the standard formula for the surface area of a sphere: 4πr².
//
// The implementation is straightforward - I just need to compute the formula and assign it to the return variable.

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method SphereSurfaceArea(radius: real) returns (area: real)
    requires radius > 0.0
    ensures area == 4.0 * 3.14159265358979323846 * radius * radius
// </vc-spec>
// <vc-code>
{
  area := 4.0 * 3.14159265358979323846 * radius * radius;
}
// </vc-code>