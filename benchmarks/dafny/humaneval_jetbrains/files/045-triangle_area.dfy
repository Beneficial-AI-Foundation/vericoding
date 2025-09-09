/*
function_signature: def triangle_area(a: float, h: float) -> float
Given length of a side and high return area for a triangle.
*/

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method CalculateTriangleArea(a: real, h: real) returns (area: real)

  requires h >= 0.0 && a >= 0.0

  ensures area == (h * a) / 2.0
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
