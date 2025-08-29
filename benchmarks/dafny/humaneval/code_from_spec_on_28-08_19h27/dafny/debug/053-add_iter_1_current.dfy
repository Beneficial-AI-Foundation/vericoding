// <vc-helpers>
// </vc-helpers>

// <vc-description>
/*
function_signature: def add(x: Int, y: Int) -> Int
*/
// </vc-description>

// <vc-spec>
method add(x: int, y: int) returns (result: int)
  ensures result == x + y
// </vc-spec>
// <vc-code>
{
  result := x + y;
}
// </vc-code>
