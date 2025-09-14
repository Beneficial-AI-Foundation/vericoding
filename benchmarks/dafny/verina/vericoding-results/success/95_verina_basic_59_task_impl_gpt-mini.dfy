// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function Twice(a: int): int { 2 * a }
// </vc-helpers>

// <vc-spec>
method DoubleQuadruple(x: int) returns (result: (int, int))
    ensures result.0 == 2 * x
    ensures result.1 == 2 * result.0
// </vc-spec>
// <vc-code>
{
  result := (Twice(x), Twice(Twice(x)));
}
// </vc-code>
