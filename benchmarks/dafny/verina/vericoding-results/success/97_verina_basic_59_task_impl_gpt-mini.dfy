// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function double(n: int): int { 2 * n }
// </vc-helpers>

// <vc-spec>
method DoubleQuadruple(x: int) returns (result: (int, int))
    ensures result.0 == 2 * x
    ensures result.1 == 2 * result.0
// </vc-spec>
// <vc-code>
{
  var d := double(x);
  result := (d, double(d));
}
// </vc-code>
