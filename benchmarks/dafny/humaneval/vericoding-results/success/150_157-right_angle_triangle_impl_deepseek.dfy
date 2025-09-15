// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function square(x: int): int { x * x }
predicate IsRightAngle(a: int, b: int, c: int) { square(a) + square(b) == square(c) }
// </vc-helpers>

// <vc-spec>
method right_angle_triangle(a : int, b : int, c : int) returns (result : bool)

  ensures result == (a * a + b * b == c * c || a * a + c * c == b * b || b * b + c * c == a * a)
// </vc-spec>
// <vc-code>
{
  var a2 := square(a);
  var b2 := square(b);
  var c2 := square(c);
  result := (a2 + b2 == c2) || (a2 + c2 == b2) || (b2 + c2 == a2);
}
// </vc-code>
