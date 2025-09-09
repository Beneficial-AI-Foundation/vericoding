/*
function_signature: def add(x: Int, y: Int) -> Int
*/

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method add(x: int, y: int) returns (z: int)
  // post-conditions-start
  ensures z == x + y
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
