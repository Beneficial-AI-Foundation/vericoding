// <vc-helpers>
// No additional helpers or proofs needed for this implementation
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method DoubleQuadruple(x: int) returns (a: int, b: int)
  ensures a == 2 * x && b == 4 * x
// </vc-spec>
// </vc-spec>

// <vc-code>
method DoubleQuadrupleImpl(x: int) returns (a: int, b: int)
  ensures a == 2 * x && b == 4 * x
{
  a := x + x;
  b := a + a;
}
// </vc-code>
