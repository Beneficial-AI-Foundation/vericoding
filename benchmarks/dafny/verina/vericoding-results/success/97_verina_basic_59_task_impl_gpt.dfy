// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function Double(n: int): int { 2 * n }
// </vc-helpers>

// <vc-spec>
method DoubleQuadruple(x: int) returns (result: (int, int))
    ensures result.0 == 2 * x
    ensures result.1 == 2 * result.0
// </vc-spec>
// <vc-code>
{
  var d := 2 * x;
  result := (d, 2 * d);
}
// </vc-code>
