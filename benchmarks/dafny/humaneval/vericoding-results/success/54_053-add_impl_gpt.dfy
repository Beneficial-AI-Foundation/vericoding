// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function add2(a: int, b: int): int { a + b }
// </vc-helpers>

// <vc-spec>
method add(x: int, y: int) returns (z: int)

  ensures z == x + y
// </vc-spec>
// <vc-code>
{
  z := x + y;
}
// </vc-code>
