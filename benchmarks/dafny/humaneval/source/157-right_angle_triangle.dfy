method right_angle_triangle(a : int, b : int, c : int) returns (result : bool)
  // post-conditions-start
  ensures result == (a * a + b * b == c * c || a * a + c * c == b * b || b * b + c * c == a * a)
  // post-conditions-end
{
  // impl-start
  result := a * a + b * b == c * c || a * a + c * c == b * b || b * b + c * c == a * a;
  // impl-end
}
