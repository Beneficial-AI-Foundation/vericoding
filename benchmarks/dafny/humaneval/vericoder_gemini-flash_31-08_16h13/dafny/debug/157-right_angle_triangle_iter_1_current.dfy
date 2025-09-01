

// <vc-helpers>
lemma Pow2(x: int) returns (y: int)
  ensures y == x * x
{
  return x * x;
}
// </vc-helpers>

// <vc-spec>
method right_angle_triangle(a : int, b : int, c : int) returns (result : bool)
  // post-conditions-start
  ensures result == (a * a + b * b == c * c || a * a + c * c == b * b || b * b + c * c == a * a)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var aSq := Pow2(a);
  var bSq := Pow2(b);
  var cSq := Pow2(c);
  result := aSq + bSq == cSq || aSq + cSq == bSq || bSq + cSq == aSq;
}
// </vc-code>

