// <vc-helpers>
// No additional helpers or proofs needed for this simple swap implementation
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method Swap(X: int, Y: int) returns(x: int, y: int)
  ensures x==Y
  ensures y==X
// </vc-spec>
// </vc-spec>

// <vc-code>
method SwapImpl(X: int, Y: int) returns (x: int, y: int)
  ensures x == Y
  ensures y == X
{
  x := Y;
  y := X;
}
// </vc-code>
