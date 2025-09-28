// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function SwapPair(x: int, y: int): (int, int)
{
  (y, x)
}
// </vc-helpers>

// <vc-spec>
method Swap(x: int, y: int) returns (result: (int, int))
    ensures
        result.0 == y &&
        result.1 == x &&
        (x != y ==> result.0 != x && result.1 != y)
// </vc-spec>
// <vc-code>
{
  result := SwapPair(x, y);
}
// </vc-code>
