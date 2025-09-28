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
function ValidTriangle_bool(a: real, b: real, c: real): bool
  ensures ValidTriangle(a, b, c) <==> ValidTriangle_bool(a, b, c)
{
  a > 0.0 && b > 0.0 && c > 0.0 && a + b > c && a + c > b && b + c > a
}

function IsRightTriangle_bool(a: real, b: real, c: real): bool
  ensures IsRightTriangle(a, b, c) <==> IsRightTriangle_bool(a, b, c)
{
  a * a + b * b == c * c || a * a + c * c == b * b || b * b + c * c == a * a
}

function ValidRightTriangle_bool(a: real, b: real, c: real): bool
  ensures ValidRightTriangle(a, b, c) <==> ValidRightTriangle_bool(a, b, c)
{
  ValidTriangle_bool(a, b, c) && IsRightTriangle_bool(a, b, c)
}
// </vc-helpers>

// <vc-spec>
method right_angle_triangle(a: real, b: real, c: real) returns (result: bool)
    ensures result <==> ValidRightTriangle(a, b, c)
// </vc-spec>
// <vc-code>
{
  result := ValidRightTriangle_bool(a, b, c);
}
// </vc-code>
