// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function TripleOf(x: int): int { 3 * x }
// </vc-helpers>

// <vc-spec>
method Triple(x: int) returns (result: int)
    ensures result == 3 * x
// </vc-spec>
// <vc-code>
{
  result := TripleOf(x);
}
// </vc-code>
