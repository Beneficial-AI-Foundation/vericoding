// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function SwapPair(a: int, b: int): (int, int)
  requires 0 <= a < 256 && 0 <= b < 256
  ensures SwapPair(a, b).0 == b && SwapPair(a, b).1 == a
{
  (b, a)
}
// </vc-helpers>

// <vc-spec>
method SwapBitvectors(x: int, y: int) returns (result: (int, int))
    requires 0 <= x < 256 && 0 <= y < 256
    ensures result.0 == y && result.1 == x
    ensures x != y ==> (result.0 != x && result.1 != y)
// </vc-spec>
// <vc-code>
{
  return (y, x);
}
// </vc-code>
