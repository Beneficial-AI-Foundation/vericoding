method Abs2(x: real) returns (y: real)
    requires x == -0.5
    ensures 0.0 <= y
    ensures 0.0 <= x ==> y == x
    ensures x < 0.0 ==> y == -x
// </vc-spec>
// <vc-code>
{
  if x >= 0.0 {
    y := x;
  } else {
    y := -x;
  }
}
// </vc-code>