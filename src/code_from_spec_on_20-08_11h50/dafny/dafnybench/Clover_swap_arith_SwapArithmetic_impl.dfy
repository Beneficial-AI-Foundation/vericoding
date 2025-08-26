method SwapArithmetic(X: int, Y: int) returns(x: int, y: int)
  ensures x==Y
  ensures y==X
// </vc-spec>
// <vc-code>
{
  x := X + Y;
  y := x - Y;
  x := x - y;
}
// </vc-code>