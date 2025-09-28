// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function triple_helper(x: int): int { x * 3 }
// </vc-helpers>

// <vc-spec>
method triple(x: int) returns (result: int)
    ensures
        result / 3 == x &&
        result / 3 * 3 == result
// </vc-spec>
// <vc-code>
{
  result := triple_helper(x);
}
// </vc-code>
