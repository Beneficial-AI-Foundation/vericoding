

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
  var aSq : int := Pow2(a);
  var bSq : int := Pow2(b);
  var cSq : int := Pow2(c);
  result := aSq + bSq == cSq || aSq + cSq == bSq || bSq + cSq == aSq;
}
// </vc-code>

