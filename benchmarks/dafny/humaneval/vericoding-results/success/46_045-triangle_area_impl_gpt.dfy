// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function TriangleArea(a: real, h: real): real { (h * a) / 2.0 }
// </vc-helpers>

// <vc-spec>
method CalculateTriangleArea(a: real, h: real) returns (area: real)

  requires h >= 0.0 && a >= 0.0

  ensures area == (h * a) / 2.0
// </vc-spec>
// <vc-code>
{
  area := TriangleArea(a, h);
}
// </vc-code>
