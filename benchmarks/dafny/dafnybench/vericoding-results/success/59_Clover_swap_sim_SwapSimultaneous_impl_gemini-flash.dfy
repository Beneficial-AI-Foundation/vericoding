

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method SwapSimultaneous(X: int, Y: int) returns(x: int, y: int)
  ensures x==Y
  ensures y==X
// </vc-spec>
// <vc-code>
{
  x := Y;
  y := X;
  return x, y;
}
// </vc-code>

