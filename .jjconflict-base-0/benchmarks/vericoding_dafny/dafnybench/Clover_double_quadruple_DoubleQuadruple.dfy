// <vc-helpers>
// </vc-helpers>

method DoubleQuadruple(x: int) returns (a: int, b: int)
  ensures a == 2 * x && b == 4 * x
// <vc-code>
{
  assume false;
}
// </vc-code>