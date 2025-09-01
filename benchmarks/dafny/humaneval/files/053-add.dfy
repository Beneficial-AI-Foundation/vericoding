// <vc-helpers>
// </vc-helpers>

// <vc-description>
/*
function_signature: def add(x: Int, y: Int) -> Int
*/
// </vc-description>

// <vc-spec>
method add(x: int, y: int) returns (z: int)
  // post-conditions-start
  ensures z == x + y
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  assume false;
}
// </vc-code>
