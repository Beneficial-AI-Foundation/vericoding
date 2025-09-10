// recursive version should be more promising

// <vc-helpers>
method gcd_pos(x: int, y: int) returns (g: int)
  requires x >= y && y > 0
  ensures g > 0
  decreases x + y
{
  var r := x % y;
  if r == 0 {
    g := y;
    return;
  }
  // Here 0 < r < y <= x, so the precondition x >= y && y > 0 holds for the recursive call gcd_pos(y, r)
  g := gcd_pos(y, r);
}
// </vc-helpers>

// <vc-spec>
method greatest_common_divisor(a: int, b: int) returns (gcd: int)
    // pre-conditions-start
    requires a != 0 || b != 0
    // pre-conditions-end
    // post-conditions-start
    ensures gcd != 0
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var x := if a < 0 then -a else a;
  var y := if b < 0 then -b else b;
  if x == 0 { gcd := y; return; }
  if y == 0 { gcd := x; return; }
  if x < y {
    var tmp := x;
    x := y;
    y := tmp;
  }
  gcd := gcd_pos(x, y);
}
// </vc-code>

