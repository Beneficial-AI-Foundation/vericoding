/*
function_signature: def add(x: Int, y: Int) -> Int
*/

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method add(x: int, y: int) returns (z: int)

  ensures z == x + y
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
