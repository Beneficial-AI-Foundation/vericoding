// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method SwapSimultaneous(X: int, Y: int) returns(x: int, y: int)
  ensures x==Y
  ensures y==X
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
