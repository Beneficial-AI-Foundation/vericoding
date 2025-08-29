// <vc-helpers>
// </vc-helpers>

// <vc-description>
/*
function_signature: def right_angle_triangle(a: Nat, b: Nat, c: Nat) -> Bool
Given the lengths of the three sides of a triangle. Return True if the three sides form a right-angled triangle, False otherwise. A right-angled triangle is a triangle in which one angle is right angle or 90 degree.
*/
// </vc-description>

// <vc-spec>
method RightAngleTriangle(a: nat, b: nat, c: nat) returns (result: bool)
  requires a > 0 && b > 0 && c > 0
  ensures result <==> (a * a + b * b == c * c || a * a + c * c == b * b || b * b + c * c == a * a)
// </vc-spec>
// <vc-code>
{
  result := (a * a + b * b == c * c) || (a * a + c * c == b * b) || (b * b + c * c == a * a);
}
// </vc-code>
