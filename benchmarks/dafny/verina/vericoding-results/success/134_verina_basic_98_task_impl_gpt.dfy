// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function triple(x: int): int { x * 3 }
// </vc-helpers>

// <vc-spec>
method Triple(x: int) returns (result: int)
    ensures result / 3 == x
    ensures result / 3 * 3 == result
// </vc-spec>
// <vc-code>
{
  result := triple(x);
}
// </vc-code>
