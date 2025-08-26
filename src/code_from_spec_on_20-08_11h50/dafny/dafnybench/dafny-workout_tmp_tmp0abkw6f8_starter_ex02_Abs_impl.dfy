method Abs(x: int) returns (y: int)
    requires x < 0
    ensures 0 < y
    ensures y == -x
// </vc-spec>
// <vc-code>
{
  y := -x;
}
// </vc-code>