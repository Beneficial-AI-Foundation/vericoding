// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function twice(a: int): int { 2 * a }
// </vc-helpers>

// <vc-spec>
method DoubleQuadruple(x: int) returns (result: (int, int))
    ensures result.0 == 2 * x
    ensures result.1 == 2 * result.0
// </vc-spec>
// <vc-code>
{
  var d := twice(x);
  result := (d, twice(d));
}
// </vc-code>
