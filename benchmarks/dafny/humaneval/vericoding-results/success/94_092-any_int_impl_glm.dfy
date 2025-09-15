// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function isSumOfOthers(x: int, y: int, z: int): bool { x == y + z }
// </vc-helpers>

// <vc-spec>
method any_int(a: int, b: int, c: int) returns (r: bool)

  ensures r == (a == b + c || b == a + c || c == a + b)
// </vc-spec>
// <vc-code>
{
  r := isSumOfOthers(a, b, c) || isSumOfOthers(b, a, c) || isSumOfOthers(c, a, b);
}
// </vc-code>
