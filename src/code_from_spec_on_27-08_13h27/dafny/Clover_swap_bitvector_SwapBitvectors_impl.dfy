// <vc-helpers>
// No additional helpers or proofs needed for this simple swap operation
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method SwapBitvectors(X: bv8, Y: bv8) returns(x: bv8, y: bv8)
  ensures x==Y
  ensures y==X
// </vc-spec>
// </vc-spec>

// <vc-code>
method SwapBitvectorsImpl(X: bv8, Y: bv8) returns (x: bv8, y: bv8)
  ensures x == Y
  ensures y == X
{
  x := Y;
  y := X;
}
// </vc-code>
