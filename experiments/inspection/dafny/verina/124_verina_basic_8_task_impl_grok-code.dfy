// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int { if a < b then a else b }
// </vc-helpers>

// <vc-spec>
method MyMin(a: int, b: int) returns (result: int)
    ensures result <= a && result <= b
    ensures result == a || result == b
// </vc-spec>
// <vc-code>
{
  result := min(a, b);
}
// </vc-code>
