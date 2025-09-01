

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
  var aSq_val := a * a;
  var bSq_val := b * b;
  var cSq_val := c * c;
  result := aSq_val + bSq_val == cSq_val || aSq_val + cSq_val == bSq_val || bSq_val + cSq_val == aSq_val;
}
// </vc-code>

