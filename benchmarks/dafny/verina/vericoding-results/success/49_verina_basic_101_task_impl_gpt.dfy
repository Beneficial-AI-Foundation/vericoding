// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function times3(x: int): int { 3 * x }
// </vc-helpers>

// <vc-spec>
method triple(x: int) returns (result: int)
    ensures
        result / 3 == x &&
        result / 3 * 3 == result
// </vc-spec>
// <vc-code>
{
  result := times3(x);
}
// </vc-code>
