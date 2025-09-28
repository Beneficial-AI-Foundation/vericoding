// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function tripleOf(x: int): int { 3 * x }
// </vc-helpers>

// <vc-spec>
method triple(x: int) returns (result: int)
    ensures
        result / 3 == x &&
        result / 3 * 3 == result
// </vc-spec>
// <vc-code>
{
  result := tripleOf(x);
}
// </vc-code>
