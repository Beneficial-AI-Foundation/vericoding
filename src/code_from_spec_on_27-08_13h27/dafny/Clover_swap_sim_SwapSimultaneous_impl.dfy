// <vc-helpers>
// No additional helper code or proofs needed for this implementation
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method SwapSimultaneous(X: int, Y: int) returns(x: int, y: int)
  ensures x==Y
  ensures y==X
// </vc-spec>
// </vc-spec>

// <vc-code>
method SwapSimultaneousImpl(X: int, Y: int) returns (x: int, y: int)
  ensures x == Y
  ensures y == X
{
  x := Y;
  y := X;
}
// </vc-code>
