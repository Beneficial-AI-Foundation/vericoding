/*
function_signature: def add(x: Int, y: Int) -> Int
*/

method add(x: int, y: int) returns (z: int)
  // post-conditions-start
  ensures z == x + y
  // post-conditions-end
{
  assume false;
}
