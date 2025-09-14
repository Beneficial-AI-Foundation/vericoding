

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method SwapBitvectors(X: bv8, Y: bv8) returns(x: bv8, y: bv8)
  ensures x==Y
  ensures y==X
// </vc-spec>
// <vc-code>
{
  x := Y;
  y := X;
}
// </vc-code>

