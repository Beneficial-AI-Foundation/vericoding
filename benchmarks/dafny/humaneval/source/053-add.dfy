method add(x: int, y: int) returns (z: int)
  // post-conditions-start
  ensures z == x + y
  // post-conditions-end
{
    // impl-start
    z := x + y;
    // impl-end
}
