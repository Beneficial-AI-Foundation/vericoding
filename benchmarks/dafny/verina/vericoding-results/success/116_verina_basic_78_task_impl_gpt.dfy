// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function Sum(a: int, b: int): int { a + b }
// </vc-helpers>

// <vc-spec>
method MultipleReturns(x: int, y: int) returns (result: (int, int))
    ensures result.0 == x + y
    ensures result.1 + y == x
// </vc-spec>
// <vc-code>
{
  result := (x + y, x - y);
}
// </vc-code>
