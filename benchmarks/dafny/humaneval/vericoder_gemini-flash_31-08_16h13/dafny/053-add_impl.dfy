

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
  return x + y;
}
// </vc-code>

