// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function triple_fn(a: int): int { a + a + a }
// </vc-helpers>

// <vc-spec>
method Triple(x: int) returns (result: int)
    ensures result == 3 * x
// </vc-spec>
// <vc-code>
{
  result := triple_fn(x);
}
// </vc-code>
