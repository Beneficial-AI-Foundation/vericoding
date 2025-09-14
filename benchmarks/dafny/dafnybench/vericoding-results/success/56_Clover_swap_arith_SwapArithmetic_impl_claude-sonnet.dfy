

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method SwapArithmetic(X: int, Y: int) returns(x: int, y: int)
  ensures x==Y
  ensures y==X
// </vc-spec>
// <vc-code>
{
  x := X;
  y := Y;
  x := x + y;
  y := x - y;
  x := x - y;
}
// </vc-code>

