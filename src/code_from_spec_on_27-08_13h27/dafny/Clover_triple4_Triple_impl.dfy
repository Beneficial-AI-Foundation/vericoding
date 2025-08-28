// <vc-helpers>
// No additional helpers or proofs needed for this simple implementation
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method Triple (x:int) returns (r:int)
  ensures r==3*x
// </vc-spec>
// </vc-spec>

// <vc-code>
method TripleImpl(x: int) returns (r: int)
  ensures r == 3 * x
{
  r := x + x + x;
}
// </vc-code>
