// <vc-helpers>
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method DoubleQuadruple(x: int) returns (a: int, b: int)
  ensures a == 2 * x && b == 4 * x
// </vc-spec>
// </vc-spec>

// <vc-code>
{
  a := 2 * x;
  b := 4 * x;
}
// </vc-code>
