// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-description>
/*
function_signature: def triangle_area(a: float, h: float) -> float
Given length of a side and high return area for a triangle.
*/
// </vc-description>

// <vc-spec>
method triangle_area(a: real, h: real) returns (area: real)
  requires a >= 0.0
  requires h >= 0.0
  ensures area == (a * h) / 2.0
  ensures area >= 0.0
// </vc-spec>
// <vc-code>
method triangle_area(a: real, h: real) returns (area: real)
  requires a >= 0.0
  requires h >= 0.0
  ensures area == (a * h) / 2.0
  ensures area >= 0.0
{
  area := (a * h) / 2.0;
}
// </vc-code>
