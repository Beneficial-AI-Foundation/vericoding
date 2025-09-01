

// <vc-helpers>
lemma SquareNonNegative(x: int)
  ensures x * x >= 0
{
}

lemma SquareOrdering(x: int, y: int)
  requires x >= 0 && y >= 0
  ensures (x <= y) <==> (x * x <= y * y)
{
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
  var a2 := a * a;
  var b2 := b * b;
  var c2 := c * c;
  
  SquareNonNegative(a);
  SquareNonNegative(b);
  SquareNonNegative(c);
  
  result := a2 + b2 == c2 || a2 + c2 == b2 || b2 + c2 == a2;
}
// </vc-code>

