// <vc-helpers>
// No additional helpers or proofs needed for this simple addition method.
// </vc-helpers>

// <vc-spec>
method add(x: int, y: int) returns (z: int)
  // post-conditions-start
  ensures z == x + y
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  z := x + y;
}
// </vc-code>
