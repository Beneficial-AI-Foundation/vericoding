// <vc-preamble>

predicate ValidTriangle(a: real, b: real, c: real)
{
    a > 0.0 && b > 0.0 && c > 0.0 &&
    a + b > c && a + c > b && b + c > a
}

predicate IsRightTriangle(a: real, b: real, c: real)
{
    a * a + b * b == c * c || 
    a * a + c * c == b * b || 
    b * b + c * c == a * a
}

predicate ValidRightTriangle(a: real, b: real, c: real)
{
    ValidTriangle(a, b, c) && IsRightTriangle(a, b, c)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method right_angle_triangle(a: real, b: real, c: real) returns (result: bool)
    ensures result <==> ValidRightTriangle(a, b, c)
// </vc-spec>
// <vc-code>
{
  if a <= 0.0 || b <= 0.0 || c <= 0.0 {
    result := false;
  } else if a + b <= c || a + c <= b || b + c <= a {
    result := false;
  } else if a * a + b * b == c * c || a * a + c * c == b * b || b * b + c * c == a * a {
    result := true;
  } else {
    result := false;
  }
}
// </vc-code>
