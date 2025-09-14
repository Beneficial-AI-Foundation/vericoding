

// <vc-helpers>
// no helpers needed
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
}
// </vc-code>

