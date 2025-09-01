

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method any_int(a: int, b: int, c: int) returns (r: bool)
  // post-conditions-start
  ensures r == (a == b + c || b == a + c || c == a + b)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  return (a == b + c) || (b == a + c) || (c == a + b);
}
// </vc-code>

