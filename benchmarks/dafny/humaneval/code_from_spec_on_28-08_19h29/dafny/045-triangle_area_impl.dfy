// <vc-helpers>
// No additional helpers needed for this simple calculation
// </vc-helpers>

// <vc-description>
/*
function_signature: def triangle_area(a: float, h: float) -> float
Given length of a side and high return area for a triangle.
*/
// </vc-description>

// <vc-spec>
method TriangleArea(a: real, h: real) returns (area: real)
  requires a >= 0.0 && h >= 0.0
  ensures area == (a * h) / 2.0
// </vc-spec>
// <vc-code>
{
  area := (a * h) / 2.0;
}
// </vc-code>
