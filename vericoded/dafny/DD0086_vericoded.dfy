

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method SwapArithmetic(X: int, Y: int) returns(x: int, y: int)
  ensures x==Y
  ensures y==X
// </vc-spec>
// <vc-code>
{
  x := Y;
  y := X;
}
// </vc-code>

