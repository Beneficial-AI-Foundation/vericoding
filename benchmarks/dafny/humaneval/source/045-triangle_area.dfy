method CalculateTriangleArea(a: real, h: real) returns (area: real)
  // pre-conditions-start
  requires h >= 0.0 && a >= 0.0
  // pre-conditions-end
  // post-conditions-start
  ensures area == (h * a) / 2.0
  // post-conditions-end
{
  // impl-start
  area := (h * a) / 2.0;
  // impl-end
}
