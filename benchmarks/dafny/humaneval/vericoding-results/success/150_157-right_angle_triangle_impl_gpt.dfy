// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function square(x: int): int { x * x }

predicate IsRightTriangle(a: int, b: int, c: int)
{
  square(a) + square(b) == square(c) ||
  square(a) + square(c) == square(b) ||
  square(b) + square(c) == square(a)
}
// </vc-helpers>

// <vc-spec>
method right_angle_triangle(a : int, b : int, c : int) returns (result : bool)

  ensures result == (a * a + b * b == c * c || a * a + c * c == b * b || b * b + c * c == a * a)
// </vc-spec>
// <vc-code>
{
  result := a * a + b * b == c * c || a * a + c * c == b * b || b * b + c * c == a * a;
}
// </vc-code>
