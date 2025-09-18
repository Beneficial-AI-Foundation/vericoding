// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function SafeMultiply(x: int, y: int): int { x * y }
// </vc-helpers>

// <vc-spec>
method Triple(x: int) returns (result: int)
    ensures result / 3 == x
    ensures result / 3 * 3 == result
// </vc-spec>
// <vc-code>
{
  result := x * 3;
}
// </vc-code>
