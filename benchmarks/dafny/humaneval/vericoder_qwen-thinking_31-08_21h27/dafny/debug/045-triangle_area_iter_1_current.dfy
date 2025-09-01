

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method CalculateTriangleArea(a: real, h: real) returns (area: real)
  // pre-conditions-start
  requires h >= 0.0 && a >= 0.0
  // pre-conditions-end
  // post-conditions-start
  ensures area == (h * a) / 2.0
  // post-conditions-end
// </vc-spec>
// <vc-code>
area := (h * a) / 2.0;
// </vc-code>

